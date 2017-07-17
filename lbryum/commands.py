import keyring
import getpass
import argparse
import ast
import base64
import copy
import datetime
import json
import logging
import sys
import time
from decimal import Decimal

from ecdsa import BadSignatureError

from lbryschema.claim import ClaimDict
from lbryschema.decode import smart_decode
from lbryschema.error import DecodeError
from lbryschema.signer import SECP256k1, get_signer
from lbryschema.uri import URIParseError, parse_lbry_uri

from lbryum import __version__
from lbryum.contacts import Contacts
from lbryum.constants import COIN, TYPE_ADDRESS, TYPE_CLAIM, TYPE_SUPPORT, TYPE_UPDATE
from lbryum.constants import RECOMMENDED_CLAIMTRIE_HASH_CONFIRMS
from lbryum.hashing import Hash, hash_160
from lbryum.claims import verify_proof
from lbryum.lbrycrd import hash_160_to_bc_address, is_address, decode_claim_id_hex
from lbryum.lbrycrd import encode_claim_id_hex, encrypt_message, public_key_from_private_key
from lbryum.lbrycrd import claim_id_hash, verify_message
from lbryum.base import base_decode
from lbryum.transaction import Transaction
from lbryum.transaction import decode_claim_script, deserialize as deserialize_transaction
from lbryum.transaction import get_address_from_output_script, script_GetOp
from lbryum.errors import InvalidProofError, NotEnoughFunds
from lbryum.util import format_satoshis, rev_hex
from lbryum.mnemonic import Mnemonic


log = logging.getLogger(__name__)

ADDRESS_LENGTH = 25
MAX_PAGE_SIZE = 500
_KEY_RING = keyring.get_keyring()


# Format output from lbrycrd to have consistently
# named ditionary keys
def format_lbrycrd_keys(obj, raw_claim=None):
    if isinstance(obj, dict):
        for key, val in obj.iteritems():
            new_key = key
            if key == 'n' or key == 'nOut':
                new_key = 'nout'
            elif key == 'nAmount':
                new_key = 'amount'
            elif key == 'nEffectiveAmount':
                new_key = 'effective_amount'
            elif key == 'claimId':
                new_key = 'claim_id'
            elif key == 'nHeight':
                new_key = 'height'
            elif key == 'nValidAtHeight':
                new_key = 'valid_at_height'
            elif key == 'nLastTakeoverHeight':
                new_key = 'last_takeover_height'
            elif key == 'supports without claims':
                new_key = 'supports_without_claims'
            elif key == 'is controlling':
                new_key = 'is_controlling'
            elif key == 'in claim trie':
                new_key = 'in_claim_trie'
            elif key == 'value' and raw_claim:
                if isinstance(val, (unicode, str)):
                    try:
                        val = val.decode('hex')
                    except ValueError:
                        pass
                    val = val.encode('hex')
                elif isinstance(val, dict) and raw_claim:
                    encoded = ClaimDict.load_dict(val).serialized.encode('hex')
                    val = encoded
            elif key == 'claims':
                val = format_lbrycrd_keys(val, raw_claim=raw_claim)
            if new_key != key:
                obj[new_key] = obj[key]
                del obj[key]
            if isinstance(val, (list, dict)):
                obj[new_key] = format_lbrycrd_keys(val, raw_claim=raw_claim)

    elif isinstance(obj, list):
        obj = [format_lbrycrd_keys(o, raw_claim=raw_claim) for o in obj]
    return obj


# Format amount to be decimal encoded string
# Format value to be hex encoded string
def format_amount_value(obj):
    if isinstance(obj, dict):
        for k, v in obj.iteritems():
            if k == 'amount' or k == 'effective_amount':
                obj[k] = float(obj[k]) / float(COIN)
            elif k == 'supports' and isinstance(v, list):
                obj[k] = [{'txid': txid, 'nout': nout, 'amount': float(amount) / float(COIN)}
                          for (txid, nout, amount) in v]
            elif isinstance(v, (list, dict)):
                obj[k] = format_amount_value(v)
    elif isinstance(obj, list):
        obj = [format_amount_value(o) for o in obj]
    return obj


def command(s):
    def decorator(func):
        func.name = func.__name__
        func.requires_network = 'n' in s
        func.requires_wallet = 'w' in s
        func.requires_password = 'p' in s
        func.description = func.__doc__
        func.help = func.__doc__.split(".")[0] if func.__doc__ else None
        varnames = func.func_code.co_varnames[1:func.func_code.co_argcount]
        func.defaults = func.func_defaults
        if func.defaults:
            n = len(func.defaults)
            func.params = list(varnames[:-n])
            func.options = list(varnames[-n:])
        else:
            func.params = list(varnames)
            func.options = []
            func.defaults = []
        func.is_command = True
        return func
    return decorator


class CommandType(type):
    """
    Metaclass used to register @command decorated methods to the `known_commands` class attribute
    """

    def __new__(mcs, *args, **kwargs):
        cls = super(CommandType, mcs).__new__(mcs, *args, **kwargs)
        cls.known_commands = {}
        for name in dir(cls):
            cmd = getattr(cls, name)
            if hasattr(cmd, "is_command"):
                cls.known_commands[cmd.__name__] = cmd
        return cls


class Commands(object):
    __metaclass__ = CommandType

    def __init__(self, config, wallet, network, callback=None, password=None, new_password=None):
        self.config = config
        self.wallet = wallet
        self.network = network
        self._callback = callback
        self.contacts = Contacts(self.config)
        self._password = None
        self.new_password = None
        if self.wallet.use_encryption and not password:
            # see if we can find the wallet password in the key ring, if not the user must
            # provide it
            password = _KEY_RING.get_password("lbryum", getpass.getuser())
            if password:
                self.unlock_wallet(password)
                log.info("unlocked the wallet using password from %s" % _KEY_RING.name)
            else:
                log.info("wallet password was not specified and is not in the keyring, "
                         "it must be provided to unlock the wallet")
        elif self.wallet.use_encryption and password:
            self.unlock_wallet(password)
        if self.wallet.use_encryption and new_password:
            self.update_password(new_password)

    @property
    def locked(self):
        return self._password is None and self.wallet.use_encryption

    def unlock_wallet(self, password):
        if self._password:
            return
        if not self.wallet.use_encryption:
            return
        self.wallet.check_password(password)
        self._password = password
        self.new_password = None
        return

    def lock_wallet(self):
        if self.locked:
            return
        self._password = None
        self.new_password = None

    def decrypt_wallet(self):
        if not self.wallet.use_encryption:
            return
        with self.wallet.storage.lock:
            self.wallet.check_password(self._password)
            self.new_password = None
            self.wallet.update_password(self._password, self.new_password)
            self.wallet.storage.write()
            self._password = None
        return

    def update_password(self, new_password, update_keyring=True):
        if not new_password:
            return
        if self.wallet.use_encryption:
            self.wallet.check_password(self._password)
        with self.wallet.storage.lock:
            self.new_password = new_password
            self.wallet.update_password(self._password, self.new_password)
            if update_keyring:
                _KEY_RING.set_password("lbryum", getpass.getuser(), new_password)
            self.wallet.storage.write()
            self._password = self.new_password
        return

    @command('')
    def commands(self):
        """List of commands"""
        return ' '.join(sorted(self.known_commands.keys()))

    @command('')
    def create(self):
        """Create a new wallet"""
        raise BaseException('Not a JSON-RPC command')

    @command('wn')
    def restore(self, text):
        """Restore a wallet from text. Text can be a seed phrase, a master
        public key, a master private key, a list of bitcoin addresses
        or bitcoin private keys. If you want to be prompted for your
        seed, type '?' or ':' (concealed) """
        raise BaseException('Not a JSON-RPC command')

    @command('w')
    def deseed(self):
        """Remove seed from wallet. This creates a seedless, watching-only
        wallet."""
        raise BaseException('Not a JSON-RPC command')

    @command('wp')
    def password(self):
        """Change wallet password. """
        self.wallet.update_password(self._password, self.new_password)
        self.wallet.storage.write()
        return {'password': self.wallet.use_encryption}

    @command('')
    def getconfig(self, key):
        """Return a configuration variable. """
        return self.config.get(key)

    @command('')
    def setconfig(self, key, value):
        """Set a configuration variable. 'value' may be a string or a Python expression."""
        try:
            value = ast.literal_eval(value)
        except:
            pass
        self.config.set_key(key, value)
        return True

    @command('')
    def make_seed(self, nbits=128, entropy=1, language=None):
        """Create a seed"""
        language = language or "en"
        s = Mnemonic(language).make_seed(nbits, custom_entropy=entropy)
        return s.encode('utf8')

    @command('')
    def check_seed(self, seed, entropy=1, language=None):
        """Check that a seed was generated with given entropy"""
        language = language or "en"
        return Mnemonic(language).check_seed(seed, entropy)

    @command('n')
    def getaddresshistory(self, address):
        """Return the transaction history of any address. Note: This is a
        walletless server query, results are not checked by SPV.
        """
        return self.network.synchronous_get(('blockchain.address.get_history', [address]))

    @command('w')
    def listunspent(self):
        """List unspent outputs. Returns the list of unspent transaction
        outputs in your wallet."""
        l = copy.deepcopy(self.wallet.get_spendable_coins(exclude_frozen=False))
        for i in l:
            v = i["value"]
            i["value"] = float(v) / COIN if v is not None else None
        return l

    @command('n')
    def getaddressunspent(self, address):
        """Returns the UTXO list of any address. Note: This
        is a walletless server query, results are not checked by SPV.
        """
        return self.network.synchronous_get(('blockchain.address.listunspent', [address]))

    @command('n')
    def getutxoaddress(self, txid, pos):
        """Get the address of a UTXO. Note: This is a walletless server query, results are
        not checked by SPV.
        """
        r = self.network.synchronous_get(('blockchain.utxo.get_address', [txid, pos]))
        return {'address': r}

    @command('wp')
    def createrawtx(self, inputs, outputs, unsigned=False):
        """Create a transaction from json inputs. The syntax is similar to bitcoind."""
        coins = self.wallet.get_spendable_coins(exclude_frozen=False)
        tx_inputs = []
        for i in inputs:
            prevout_hash = i['txid']
            prevout_n = i['vout']
            for c in coins:
                if c['prevout_hash'] == prevout_hash and c['prevout_n'] == prevout_n:
                    self.wallet.add_input_info(c)
                    tx_inputs.append(c)
                    break
            else:
                raise BaseException('Transaction output not in wallet',
                                    prevout_hash + ":%d" % prevout_n)
        outputs = map(lambda x: (TYPE_ADDRESS, x[0], int(COIN * x[1])), outputs.items())
        tx = Transaction.from_io(tx_inputs, outputs)
        if not unsigned:
            self.wallet.sign_transaction(tx, self._password)
        return tx.as_dict()

    @command('wp')
    def signtransaction(self, tx, privkey=None):
        """Sign a transaction. The wallet keys will be used unless a private key is provided."""
        t = Transaction(tx)
        if privkey:
            pubkey = public_key_from_private_key(privkey)
            t.sign({pubkey: privkey})
        else:
            self.wallet.sign_transaction(t, self._password)
        return t.as_dict()

    @command('')
    def deserialize(self, tx):
        """Deserialize a serialized transaction"""
        return Transaction(tx).deserialize()

    @command('n')
    def broadcast(self, tx):
        """Broadcast a transaction to the network. """
        t = Transaction(tx)
        return self.network.synchronous_get(('blockchain.transaction.broadcast', [str(t)]))

    @command('')
    def createmultisig(self, num, pubkeys):
        """Create multisig address"""
        assert isinstance(pubkeys, list), (type(num), type(pubkeys))
        redeem_script = Transaction.multisig_script(pubkeys, num)
        address = hash_160_to_bc_address(hash_160(redeem_script.decode('hex')), 5)
        return {'address': address, 'redeemScript': redeem_script}

    @command('w')
    def freeze(self, address):
        """Freeze address. Freeze the funds at one of your wallet\'s addresses"""
        return self.wallet.set_frozen_state([address], True)

    @command('w')
    def unfreeze(self, address):
        """Unfreeze address. Unfreeze the funds at one of your wallet\'s address"""
        return self.wallet.set_frozen_state([address], False)

    @command('wp')
    def getprivatekeys(self, address):
        """
        Get private keys of addresses. You may pass a single wallet address,
        or a list of wallet addresses.
        """

        is_list = type(address) is list
        domain = address if is_list else [address]
        out = [self.wallet.get_private_key(address, self._password) for address in domain]
        return out if is_list else out[0]

    @command('w')
    def ismine(self, address):
        """Check if address is in wallet. Return true if and only address is in wallet"""
        return self.wallet.is_mine(address)

    @command('')
    def dumpprivkeys(self):
        """Deprecated."""
        return "This command is deprecated. Use a pipe instead: " \
               "'lbryum listaddresses | lbryum getprivatekeys - '"

    @command('')
    def validateaddress(self, address):
        """Check that an address is valid. """
        return is_address(address)

    @command('w')
    def getpubkeys(self, address):
        """Return the public keys for a wallet address. """
        return self.wallet.get_public_keys(address)

    @command('w')
    def getbalance(self, account=None, exclude_claimtrietx=False):
        """Return the balance of your wallet. """
        if account is None:
            c, u, x = self.wallet.get_balance(exclude_claimtrietx=exclude_claimtrietx)
        else:
            c, u, x = self.wallet.get_account_balance(account, exclude_claimtrietx)
        out = {"confirmed": str(Decimal(c) / COIN)}
        if u:
            out["unconfirmed"] = str(Decimal(u) / COIN)
        if x:
            out["unmatured"] = str(Decimal(x) / COIN)
        return out

    @command('n')
    def getaddressbalance(self, address):
        """Return the balance of any address. Note: This is a walletless
        server query, results are not checked by SPV.
        """
        out = self.network.synchronous_get(('blockchain.address.get_balance', [address]))
        out["confirmed"] = str(Decimal(out["confirmed"]) / COIN)
        out["unconfirmed"] = str(Decimal(out["unconfirmed"]) / COIN)
        return out

    @command('n')
    def getproof(self, address):
        """Get Merkle branch of an address in the UTXO set"""
        p = self.network.synchronous_get(('blockchain.address.get_proof', [address]))
        out = []
        for i, s in p:
            out.append(i)
        return out

    @command('n')
    def getmerkle(self, txid, height):
        """Get Merkle branch of a transaction included in a block. Electrum
        uses this to verify transactions (Simple Payment Verification)."""
        return self.network.synchronous_get(
            ('blockchain.transaction.get_merkle', [txid, int(height)]))

    @command('n')
    def getservers(self):
        """Return the list of available servers"""
        while not self.network.is_up_to_date():
            time.sleep(0.1)
        return self.network.get_servers()

    @command('')
    def version(self):
        """Return the version of lbryum."""
        return __version__

    @command('w')
    def getmpk(self):
        """Get master public key. Return your wallet\'s master public key(s)"""
        return self.wallet.get_master_public_keys()

    @command('wp')
    def getmasterprivate(self):
        """Get master private key. Return your wallet\'s master private key"""
        return str(self.wallet.get_master_private_key(self.wallet.root_name, self._password))

    @command('wp')
    def getseed(self):
        """Get seed phrase. Print the generation seed of your wallet."""
        s = self.wallet.get_mnemonic(self._password)
        return s.encode('utf8')

    @command('wp')
    def importprivkey(self, privkey):
        """Import a private key. """
        try:
            addr = self.wallet.import_key(privkey, self._password)
            out = "Keypair imported: " + addr
        except Exception as e:
            out = "Error: " + str(e)
        return out

    def _resolver(self, x):
        if x is None:
            return None
        out = self.contacts.resolve(x)
        if out.get('type') == 'openalias' and self.nocheck is False and out.get(
                'validated') is False:
            raise BaseException('cannot verify alias', x)
        return out['address']

    @command('n')
    def sweep(self, privkey, destination, tx_fee=None, nocheck=False):
        """Sweep private keys. Returns a transaction that spends UTXOs from
        privkey to a destination address. The transaction is not
        broadcasted."""
        privkeys = privkey if type(privkey) is list else [privkey]
        self.nocheck = nocheck
        dest = self._resolver(destination)
        if tx_fee is None:
            tx_fee = 0.0001
        fee = int(Decimal(tx_fee) * COIN)
        return Transaction.sweep(privkeys, self.network, dest, fee)

    @command('wp')
    def signmessage(self, address, message):
        """Sign a message with a key. Use quotes if your message contains
        whitespaces"""
        sig = self.wallet.sign_message(address, message, self._password)
        return base64.b64encode(sig)

    @command('')
    def verifymessage(self, address, signature, message):
        """Verify a signature."""
        sig = base64.b64decode(signature)
        return verify_message(address, sig, message)

    def _mktx(self, outputs, fee, change_addr, domain, nocheck, unsigned, claim_name=None,
              claim_val=None,
              abandon_txid=None, claim_id=None):
        self.nocheck = nocheck
        change_addr = self._resolver(change_addr)
        domain = None if domain is None else map(self._resolver, domain)
        fee = None if fee is None else int(COIN * Decimal(fee))
        final_outputs = []
        for address, amount in outputs:
            address = self._resolver(address)
            # assert self.wallet.is_mine(address)
            if amount == '!':
                assert len(outputs) == 1
                inputs = self.wallet.get_spendable_coins(domain)
                amount = sum(map(lambda x: x['value'], inputs))
                if fee is None:
                    for i in inputs:
                        self.wallet.add_input_info(i)
                    output = (TYPE_ADDRESS, address, amount)
                    dummy_tx = Transaction.from_io(inputs, [output])
                    fee_per_kb = self.wallet.fee_per_kb(self.config)
                    fee = dummy_tx.estimated_fee(self.wallet.relayfee(), fee_per_kb)
                amount -= fee
            else:
                amount = int(COIN * Decimal(amount))
            txout_type = TYPE_ADDRESS
            val = address
            if claim_name is not None and claim_val is not None and claim_id is not None\
                    and abandon_txid is not None:
                assert len(outputs) == 1
                txout_type |= TYPE_UPDATE
                val = ((claim_name, claim_id, claim_val), val)
            elif claim_name is not None and claim_id is not None:
                assert len(outputs) == 1
                txout_type |= TYPE_SUPPORT
                val = ((claim_name, claim_id), val)
            elif claim_name is not None and claim_val is not None:
                assert len(outputs) == 1
                txout_type |= TYPE_CLAIM
                val = ((claim_name, claim_val), val)
            final_outputs.append((txout_type, val, amount))

        coins = self.wallet.get_spendable_coins(domain, abandon_txid=abandon_txid)
        tx = self.wallet.make_unsigned_transaction(coins, final_outputs, self.config, fee,
                                                   change_addr,
                                                   abandon_txid=abandon_txid)
        str(tx)  # this serializes
        if not unsigned:
            self.wallet.sign_transaction(tx, self._password)

        return tx

    @command('wp')
    def getunusedaddress(self, account=None):
        addr = self.wallet.get_unused_address(account)
        if addr is None:
            addr = self.wallet.create_new_address()
            self.wallet.storage.write()
        return addr

    @command('wp')
    def payto(self, destination, amount, tx_fee=None, from_addr=None, change_addr=None,
              nocheck=False, unsigned=False):
        """Create a raw transaction. """
        domain = [from_addr] if from_addr else None
        tx = self._mktx([(destination, amount)], tx_fee, change_addr, domain, nocheck, unsigned)
        return tx.as_dict()

    @command('wpn')
    def paytoandsend(self, destination, amount, tx_fee=None, from_addr=None, change_addr=None,
                     nocheck=False, unsigned=False):
        """Create and broadcast transaction. """
        domain = [from_addr] if from_addr else None
        tx = self._mktx([(destination, amount)], tx_fee, change_addr, domain, nocheck, unsigned)
        return self.network.synchronous_get(('blockchain.transaction.broadcast', [str(tx)]))

    @command('w')
    def waitfortxinwallet(self, txid, timeout=30):
        """
        wait for tx with txid to appear in wallet for timeout seconds
        return True, if txid appears within timeout, return False otherwise
        """
        start_time = time.time()
        while start_time - time.time() < timeout:
            if txid in self.wallet.transactions:
                return True
            time.sleep(0.2)
        return False

    @command('wpn')
    def sendclaimtoaddress(self, claim_id, destination, amount, tx_fee=None, change_addr=None,
                           broadcast=True):
        claims = self.getnameclaims(raw=True, include_supports=False, claim_id=claim_id)
        if len(claims) > 1:
            return {"success": False, 'reason': 'more than one claim that matches'}
        elif len(claims) == 0:
            return {"success": False, 'reason': 'claim not found', 'claim_id': claim_id}
        else:
            claim = claims[0]

        txid = claim['txid']
        nout = claim['nout']
        claim_name = claim['name']
        claim_val = claim['value']
        return self.update(claim_name, claim_val, amount=amount, certificate_id=None,
                           claim_id=claim_id, txid=txid, nout=nout, broadcast=broadcast,
                           claim_addr=destination, tx_fee=tx_fee, change_addr=change_addr,
                           raw=False, skip_validate_schema=True)

    @command('wp')
    def paytomany(self, outputs, tx_fee=None, from_addr=None, change_addr=None, nocheck=False,
                  unsigned=False):
        """Create a multi-output transaction. """
        domain = [from_addr] if from_addr else None
        tx = self._mktx(outputs, tx_fee, change_addr, domain, nocheck, unsigned)
        return tx.as_dict()

    @command('wp')
    def paytomanyandsend(self, outputs, tx_fee=None, from_addr=None, change_addr=None,
                         nocheck=False, unsigned=False):
        """Create and broadcast a multi-output transaction. """
        domain = [from_addr] if from_addr else None
        tx = self._mktx(outputs, tx_fee, change_addr, domain, nocheck, unsigned)
        return self.network.synchronous_get(('blockchain.transaction.broadcast', [str(tx)]))

    @command('w')
    def history(self):
        """Wallet history. Returns the transaction history of your wallet."""
        balance = 0
        out = []
        for item in self.wallet.get_history():
            tx_hash, conf, value, timestamp, balance = item
            try:
                time_str = datetime.datetime.fromtimestamp(timestamp).isoformat(' ')[:-3]
            except Exception:
                time_str = "----"
            label = self.wallet.get_label(tx_hash)
            out.append({
                'txid': tx_hash,
                'timestamp': timestamp,
                'date': "%16s" % time_str,
                'label': label,
                'value': float(value) / COIN if value is not None else None,
                'confirmations': conf}
            )
        return out

    @command('w')
    def setlabel(self, key, label):
        """Assign a label to an item. Item may be a bitcoin address or a
        transaction ID"""
        self.wallet.set_label(key, label)

    @command('')
    def listcontacts(self):
        """Show your list of contacts"""
        return self.contacts

    @command('')
    def getalias(self, key):
        """Retrieve alias. Lookup in your list of contacts, and for an OpenAlias DNS record."""
        return self.contacts.resolve(key)

    @command('')
    def searchcontacts(self, query):
        """Search through contacts, return matching entries. """
        results = {}
        for key, value in self.contacts.items():
            if query.lower() in key.lower():
                results[key] = value
        return results

    @command('w')
    def listaddresses(self, receiving=False, change=False, show_labels=False, frozen=False,
                      unused=False, funded=False, show_balance=False):
        """
        List wallet addresses. Returns the list of all addresses in your wallet.
        Use optional arguments to filter the results.
        """

        out = []
        for addr in self.wallet.addresses(True):
            if frozen and not self.wallet.is_frozen(addr):
                continue
            if receiving and self.wallet.is_change(addr):
                continue
            if change and not self.wallet.is_change(addr):
                continue
            if unused and self.wallet.is_used(addr):
                continue
            if funded and self.wallet.is_empty(addr):
                continue
            item = addr
            if show_balance:
                item += ", " + format_satoshis(sum(self.wallet.get_addr_balance(addr)))
            if show_labels:
                item += ', ' + repr(self.wallet.labels.get(addr, ''))
            out.append(item)
        return out

    @command('w')
    def gettransaction(self, txid):
        """Retrieve a transaction in deserialized json format"""
        tx = self.wallet.transactions.get(txid) if self.wallet else None
        if tx is None and self.network:
            raw = self.network.synchronous_get(('blockchain.transaction.get', [txid]))
            if raw:
                tx = Transaction(raw)
            else:
                raise BaseException("Unknown transaction")
        return deserialize_transaction(str(tx))

    @command('')
    def encrypt(self, pubkey, message):
        """Encrypt a message with a public key. Use quotes if the message contains whitespaces."""
        return encrypt_message(message, pubkey)

    @command('wp')
    def decrypt(self, pubkey, encrypted):
        """Decrypt a message encrypted with a public key."""
        return self.wallet.decrypt_message(pubkey, encrypted, self._password)

    @command('n')
    def notify(self, address, URL):
        """Watch an address. Everytime the address changes, a http POST is sent to the URL."""

        def callback(x):
            import urllib2
            headers = {'content-type': 'application/json'}
            data = {'address': address, 'status': x.get('result')}
            try:
                req = urllib2.Request(URL, json.dumps(data), headers)
                response_stream = urllib2.urlopen(req)
                log.info('Got Response for %s' % address)
            except BaseException as e:
                log.error(str(e))

        self.network.send([('blockchain.address.subscribe', [address])], callback)
        return True

    def validate_claim_signature_and_get_channel_name(self, claim, certificate_claim,
                                                      claim_address):
        certificate = smart_decode(certificate_claim['value'])
        if Commands._validate_signed_claim(claim, claim_address, certificate):
            return True, certificate_claim['name']
        return False, None

    def parse_and_validate_claim_result(self, claim_result, certificate=None, raw=False):
        if not claim_result or 'value' not in claim_result:
            return claim_result

        claim_result['decoded_claim'] = False
        decoded = None

        if not raw:
            claim_value = claim_result['value']
            try:
                decoded = smart_decode(claim_value)
                claim_result['value'] = decoded.claim_dict
                claim_result['decoded_claim'] = True
            except DecodeError:
                pass

        if decoded:
            claim_result['has_signature'] = False
            if decoded.has_signature:
                if certificate is None:
                    log.info("fetching certificate to check claim signature")
                    certificate = self.getclaimbyid(decoded.certificate_id)
                    if not certificate:
                        raise Exception(
                            'Certificate claim {} not found'.format(decoded.certificate_id))
                claim_result['has_signature'] = True
                claim_result['signature_is_valid'] = False
                validated, channel_name = self.validate_claim_signature_and_get_channel_name(
                    decoded, certificate, claim_result['address'])
                claim_result['channel_name'] = channel_name
                if validated:
                    claim_result['signature_is_valid'] = True

        if 'height' in claim_result and claim_result['height'] is None:
            claim_result['height'] = -1

        return claim_result

    @staticmethod
    def _validate_signed_claim(claim, claim_address, certificate):
        assert claim.has_signature, "Claim is not signed"
        if not base_decode(claim_address, ADDRESS_LENGTH, 58):
            raise Exception("Not given a valid claim address")
        try:
            if claim.validate_signature(claim_address, certificate.protobuf):
                return True
        except BadSignatureError:
            # print_msg("Signature for %s is invalid" % claim_id)
            return False
        except Exception as err:
            log.error("Signature for %s is invalid, reason: %s - %s", claim_address,
                      str(type(err)), err)
            return False
        return False

    @staticmethod
    def _verify_proof(name, claim_trie_root, result, height, depth):
        """
        Verify proof for name claim
        """

        def _build_response(name, value, claim_id, txid, n, amount, effective_amount,
                            claim_sequence, claim_address, supports):
            r = {
                'name': name,
                'value': value.encode('hex'),
                'claim_id': claim_id,
                'txid': txid,
                'nout': n,
                'amount': str(Decimal(amount) / COIN),
                'effective_amount': str(Decimal(effective_amount) / COIN),
                'height': height,
                'depth': depth,
                'claim_sequence': claim_sequence,
                'address': claim_address,
                'supports': supports
            }
            return r

        def _parse_proof_result(name, result):
            support_amount = sum(samount for stxid, sn, samount in result['supports'])
            supports = [{'txid': stxid, 'nout': snout, 'amount': float(samount) / float(COIN)}
                        for (stxid, snout, samount) in result['supports']]
            if 'txhash' in result['proof'] and 'nOut' in result['proof']:
                if 'transaction' in result:
                    computed_txhash = Hash(result['transaction'].decode('hex'))[::-1].encode('hex')
                    tx = deserialize_transaction(result['transaction'])
                    nOut = result['proof']['nOut']
                    if result['proof']['txhash'] == computed_txhash:
                        if 0 <= nOut < len(tx['outputs']):
                            scriptPubKey = tx['outputs'][nOut]['scriptPubKey']
                            amount = tx['outputs'][nOut]['value']
                            effective_amount = amount + support_amount
                            decoded_script = [r for r in script_GetOp(scriptPubKey.decode('hex'))]
                            decode_out = decode_claim_script(decoded_script)
                            decode_address = get_address_from_output_script(
                                scriptPubKey.decode('hex'))
                            claim_address = decode_address[1][1]
                            claim_id = result['claim_id']
                            claim_sequence = result['claim_sequence']
                            if decode_out is False:
                                return {'error': 'failed to decode as claim script'}
                            n, script = decode_out
                            decoded_name, decoded_value = n.name, n.value
                            if decoded_name == name:
                                return _build_response(name, decoded_value, claim_id,
                                                       computed_txhash, nOut, amount,
                                                       effective_amount, claim_sequence,
                                                       claim_address, supports)
                            return {'error': 'name in proof did not match requested name'}
                        outputs = len(tx['outputs'])
                        return {'error': 'invalid nOut: %d (let(outputs): %d' % (nOut, outputs)}
                    return {'error': "computed txid did not match given transaction: %s vs %s" %
                                     (computed_txhash, result['proof']['txhash'])
                            }
                return {'error': "didn't receive a transaction with the proof"}
            return {'error': 'name is not claimed'}

        if 'proof' in result:
            try:
                verify_proof(result['proof'], claim_trie_root, name)
            except InvalidProofError:
                return {'error': "Proof was invalid"}
            return _parse_proof_result(name, result)
        else:
            return {'error': "proof not in result"}

    @command('n')
    def requestvalueforname(self, name, blockhash):
        """
        Request and return value of name with proof from lbryum server without verifying proof
        """

        if not name:
            return {'error': 'no name to request'}
        log.info('Requesting value for name: %s, blockhash: %s', name, blockhash)
        return self.network.synchronous_get(('blockchain.claimtrie.getvalue', [name, blockhash]))

    @command('n')
    def getvalueforname(self, name, raw=False):
        """
        Request value of name from lbryum server and verify its proof
        """

        height = self.network.get_local_height() - RECOMMENDED_CLAIMTRIE_HASH_CONFIRMS + 1
        block_header = self.network.blockchain.read_header(height)
        block_hash = self.network.blockchain.hash_header(block_header)
        response = self.requestvalueforname(name, block_hash)
        height, depth = None, None
        if response and 'height' in response:
            height = response['height']
            depth = self.network.get_server_height() - height
        result = Commands._verify_proof(name, block_header['claim_trie_root'], response,
                                        height, depth)
        return self.parse_and_validate_claim_result(result, raw=raw)

    @command('n')
    def getclaimbynameinchannel(self, uri, name, raw=False):
        """
        Get claim by name within a channel by uri
        """

        channel_claims = self.getclaimsinchannel(uri, raw)
        if 'error' in channel_claims:
            return channel_claims
        for claim in channel_claims:
            if claim['name'] == name:
                return claim
        return {'success': False, 'error': 'claim not found', 'name': name}

    @command('wn')
    def getdefaultcertificate(self):
        """
        Get the claim id of the default certificate used for claim signing, if there is one
        """

        certificate_id = self.wallet.default_certificate_claim
        if not certificate_id:
            return {'error': 'no default certificate configured'}
        return self.getclaimbyid(certificate_id)

    @staticmethod
    def prepare_claim_queries(start_position, query_size, channel_claim_infos):
        queries = [tuple()]
        names = {}
        # a table of index counts for the sorted claim ids, including ignored claims
        absolute_position_index = {}

        block_sorted_infos = sorted(channel_claim_infos.iteritems(), key=lambda x: int(x[1][1]))
        per_block_infos = {}
        for claim_id, (name, height) in block_sorted_infos:
            claims = per_block_infos.get(height, [])
            claims.append((claim_id, name))
            per_block_infos[height] = sorted(claims, key=lambda x: int(x[0], 16))

        abs_position = 0

        for height in sorted(per_block_infos.keys()):
            for claim_id, name in per_block_infos[height]:
                names[claim_id] = name
                absolute_position_index[claim_id] = abs_position
                if abs_position >= start_position:
                    if len(queries[-1]) >= query_size:
                        queries.append(tuple())
                    queries[-1] += (claim_id,)
                abs_position += 1
        return queries, names, absolute_position_index

    def iter_channel_claims_pages(self, queries, claim_positions, claim_names, certificate,
                                  page_size=10):
        # lbryum server returns a dict of {claim_id: (name, claim_height)}
        # first, sort the claims by block height (and by claim id int value within a block).

        # map the sorted claims into getclaimsbyids queries of query_size claim ids each

        # send the batched queries to lbryum server and iteratively validate and parse
        # the results, yield a page of results at a time.

        # these results can include those where `signature_is_valid` is False. if they are skipped,
        # page indexing becomes tricky, as the number of results isn't known until after having
        # processed them.
        # TODO: fix ^ in lbryschema

        def iter_validate_channel_claims():
            for claim_ids in queries:
                batch_result = self.network.synchronous_get(
                    ("blockchain.claimtrie.getclaimsbyids", claim_ids))
                for claim_id in claim_ids:
                    claim = batch_result[claim_id]
                    if claim['name'] == claim_names[claim_id]:
                        formatted_claim = self.parse_and_validate_claim_result(claim, certificate)
                        formatted_claim['absolute_channel_position'] = claim_positions[
                            claim['claim_id']]
                        yield format_amount_value(formatted_claim)
                    else:
                        log.warning("ignoring claim with name mismatch %s %s", claim['name'],
                                    claim['claim_id'])

        yielded_page = False
        results = []
        for claim in iter_validate_channel_claims():
            results.append(claim)

            # if there is a full page of results, yield it
            if len(results) and len(results) % page_size == 0:
                yield results[-page_size:]
                yielded_page = True

        # if we didn't get a full page of results, yield what results we did get
        if not yielded_page:
            yield results

    def get_channel_claims_page(self, channel_claim_infos, certificate, page, page_size=10):
        page = page or 0
        page_size = max(page_size, 1)
        if page_size > MAX_PAGE_SIZE:
            raise Exception("page size above maximum allowed")
        start_position = (page - 1) * page_size
        queries, names, claim_positions = self.prepare_claim_queries(start_position, page_size,
                                                                     channel_claim_infos)
        page_generator = self.iter_channel_claims_pages(queries, claim_positions, names,
                                                        certificate, page_size=page_size)
        upper_bound = len(claim_positions)
        if not page:
            return None, upper_bound
        if start_position > upper_bound:
            raise IndexError("claim %i greater than max %i" % (start_position, upper_bound))
        return next(page_generator), upper_bound

    def _handle_resolve_uri_response(self, parsed_uri, block_header, raw, resolution, page=0,
                                     page_size=10):
        result = {}
        # parse an included certificate
        if 'certificate' in resolution:
            certificate_response = resolution['certificate']['result']
            certificate_resolution_type = resolution['certificate']['resolution_type']
            if certificate_resolution_type == "winning" and certificate_response:
                if 'height' in certificate_response:
                    height = certificate_response['height']
                    depth = self.network.get_server_height() - height
                    certificate_result = Commands._verify_proof(parsed_uri.name,
                                                                block_header['claim_trie_root'],
                                                                certificate_response,
                                                                height, depth)
                    result['certificate'] = self.parse_and_validate_claim_result(certificate_result,
                                                                                 raw=raw)
            elif certificate_resolution_type == "claim_id":
                result['certificate'] = self.parse_and_validate_claim_result(certificate_response,
                                                                             raw=raw)
            elif certificate_resolution_type == "sequence":
                result['certificate'] = self.parse_and_validate_claim_result(certificate_response,
                                                                             raw=raw)
            else:
                log.error("unknown response type: %s", certificate_resolution_type)

            if 'certificate' in result:
                certificate = result['certificate']
                if 'unverified_claims_in_channel' in resolution:
                    max_results = len(resolution['unverified_claims_in_channel'])
                    max_pages = 1 + int((max_results - (max_results % page_size)) / page_size)
                    result['claims_in_channel_pages'] = max_pages
                else:
                    result['claims_in_channel_pages'] = 0
            else:
                result['error'] = "claim not found"
                result['success'] = False
                result['uri'] = str(parsed_uri)

        else:
            certificate = None

        # if this was a resolution for a name, parse the result
        if 'claim' in resolution:
            claim_response = resolution['claim']['result']
            claim_resolution_type = resolution['claim']['resolution_type']
            if claim_resolution_type == "winning" and claim_response:
                if 'height' in claim_response:
                    height = claim_response['height']
                    depth = self.network.get_server_height() - height
                    claim_result = Commands._verify_proof(parsed_uri.name,
                                                          block_header['claim_trie_root'],
                                                          claim_response,
                                                          height, depth)
                    result['claim'] = self.parse_and_validate_claim_result(claim_result,
                                                                           certificate,
                                                                           raw)
            elif claim_resolution_type == "claim_id":
                result['claim'] = self.parse_and_validate_claim_result(claim_response,
                                                                       certificate,
                                                                       raw)
            elif claim_resolution_type == "sequence":
                result['claim'] = self.parse_and_validate_claim_result(claim_response,
                                                                       certificate,
                                                                       raw)
            else:
                log.error("unknown response type: %s", claim_resolution_type)

        # if this was a resolution for a name in a channel make sure there is only one valid
        # match
        elif 'unverified_claims_for_name' in resolution and 'certificate' in result:
            unverified_claims_for_name = resolution['unverified_claims_for_name']

            channel_info = self.get_channel_claims_page(unverified_claims_for_name,
                                                        result['certificate'], page=1)
            claims_in_channel, upper_bound = channel_info

            if len(claims_in_channel) > 1:
                log.error("Multiple signed claims for the same name")
            elif not claims_in_channel:
                log.error("No valid claims for this name for this channel")
            else:
                result['claim'] = claims_in_channel[0]

        # parse and validate claims in a channel iteratively into pages of results
        elif 'unverified_claims_in_channel' in resolution and 'certificate' in result:
            ids_to_check = resolution['unverified_claims_in_channel']
            channel_info = self.get_channel_claims_page(ids_to_check, result['certificate'],
                                                        page=page, page_size=page_size)
            claims_in_channel, upper_bound = channel_info

            if claims_in_channel:
                result['claims_in_channel'] = claims_in_channel
        elif 'error' not in result:
            result['error'] = "claim not found"
            result['success'] = False
            result['uri'] = str(parsed_uri)

        return result

    @command('n')
    def getvalueforuri(self, uri, raw=False, page=0, page_size=10):
        """
        Resolve a LBRY URI
        """

        result = self.getvaluesforuris(raw, page, page_size, uri)
        if uri in result:
            return result[uri]
        return result

    @command('n')
    def getvaluesforuris(self, raw=False, page=0, page_size=10, *uris):
        """
        Resolve a LBRY URI
        """

        page = int(page)
        page_size = int(page_size)
        uris_to_send = ()

        for uri in uris:
            try:
                parse_lbry_uri(uri)
                uris_to_send += (str(uri),)
            except URIParseError as err:
                return {'error': err.message}

        height = self.network.get_local_height() - RECOMMENDED_CLAIMTRIE_HASH_CONFIRMS + 1
        block_header = self.network.blockchain.read_header(height)
        block_hash = self.network.blockchain.hash_header(block_header)
        response = self.network.synchronous_get(('blockchain.claimtrie.getvaluesforuris',
                                                 (block_hash,) + uris_to_send))
        result = {}
        for uri, resolution in response.iteritems():
            result[uri] = self._handle_resolve_uri_response(parse_lbry_uri(str(uri)), block_header,
                                                            raw, resolution, page=page,
                                                            page_size=page_size)
        return result

    @command('n')
    def getsignaturebyid(self, claim_id):
        """
        Get signature information for a claim by its claim id
        """

        response = {'has_signature': False}
        raw_claim = self.getclaimbyid(claim_id, raw=True)

        if raw_claim:
            try:
                decoded_claim = smart_decode(raw_claim['value'].decode('hex'))
                response['decoded_claim'] = True
            except DecodeError:
                response['decoded_claim'] = False
                response['error'] = "Could not decode claim value"
            if response['decoded_claim'] and decoded_claim.has_signature:
                response['has_signature'] = True
                response['signature'] = decoded_claim.signature
                response['certificate'] = self.getclaimbyid(decoded_claim.certificate_id)
                validated, channel_name = self.validate_claim_signature_and_get_channel_name(
                    decoded_claim, response['certificate'], raw_claim['address'])
                response['channel_name'] = channel_name
                if validated:
                    response['signature_is_valid'] = True
                else:
                    response['signature_is_valid'] = False
            else:
                response['has_signature'] = False
        else:
            response['error'] = "claim does not exist"
        return response

    @command('n')
    def getclaimsfromtx(self, txid, raw=False):
        """
        Return the claims which are in a transaction
        """

        out = self.network.synchronous_get(('blockchain.claimtrie.getclaimsintx', [txid]))
        result = format_amount_value(format_lbrycrd_keys(out, raw))
        return self.parse_and_validate_claim_result(result, raw=raw)

    @command('n')
    def getclaimbyoutpoint(self, txid, nout, raw=False):
        """
        Return claim at outpoint (txid:nout)
        If no claim exists at outpoint, or outpoint not found, return
        dictionary where 'success' is False and 'error' is 'claim not found'
        """

        out = self.network.synchronous_get(('blockchain.claimtrie.getclaimsintx', [txid]))
        claims = format_amount_value(format_lbrycrd_keys(out, raw))
        claim_not_found_out = {'success': False, 'error': 'claim not found',
                               'outpoint': '%s:%i' % (txid, nout)}
        if claims is None:
            return claim_not_found_out
        for claim in claims:
            if claim['nout'] == nout:
                return self.parse_and_validate_claim_result(claim, raw=raw)
        return claim_not_found_out

    @command('n')
    def getclaimsforname(self, name, raw=False):
        """
        Return all claims and supports for a name
        """

        out = self.network.synchronous_get(('blockchain.claimtrie.getclaimsforname', [name]))
        result = format_lbrycrd_keys(out, raw)
        claims = format_amount_value(result['claims'])
        claims_for_return = []
        for claim in claims:
            claims_for_return.append(self.parse_and_validate_claim_result(claim, raw=raw))
        result['claims'] = claims_for_return
        return result

    @command('n')
    def getclaimssignedby(self, claim_id, raw=False):
        """
        Request claims signed by a given certificate
        """

        result = self.network.synchronous_get(('blockchain.claimtrie.getclaimssignedbyid',
                                               [claim_id]))
        claims = format_amount_value(result)
        return [self.parse_and_validate_claim_result(claim, raw=raw) for claim in claims]

    @command('n')
    def getclaimsinchannel(self, uri, raw=False):
        """
        Get claims in a channel for a uri
        """

        parsed = parse_lbry_uri(uri)
        if not parsed.is_channel:
            return {'error': 'not a channel uri'}
        elif parsed.claim_sequence is not None:
            claims = self.network.synchronous_get(
                ('blockchain.claimtrie.getclaimssignedbynthtoname',
                 [parsed.name, parsed.claim_sequence]))
        elif parsed.claim_id is not None:
            claims = self.network.synchronous_get(('blockchain.claimtrie.getclaimssignedbyid',
                                                   [parsed.claim_id]))
        else:
            claims = self.network.synchronous_get(('blockchain.claimtrie.getclaimssignedby',
                                                   [parsed.name]))
        if claims:
            result = format_amount_value(claims)
            return [self.parse_and_validate_claim_result(claim, raw=raw) for claim in result]
        return []

    @command('n')
    def getblock(self, blockhash):
        """
        Return a block matching the given blockhash
        """

        return self.network.synchronous_get(('blockchain.block.get_block', [blockhash]))

    @command('n')
    def getbestblockhash(self):
        height = self.network.get_local_height()
        if height < 0:
            return None
        header = self.network.blockchain.read_header(height)
        return self.network.blockchain.hash_header(header)

    @command('n')
    def getmostrecentblocktime(self):
        height = self.network.get_local_height()
        if height < 0:
            return None
        header = self.network.get_header(self.network.get_local_height())
        return header['timestamp']

    @command('n')
    def getnetworkstatus(self):
        out = {'is_connecting': self.network.is_connecting(),
               'is_connected': self.network.is_connected(),
               'local_height': self.network.get_local_height(),
               'server_height': self.network.get_server_height(),
               'blocks_behind': self.network.get_blocks_behind(),
               'retrieving_headers': self.network.blockchain.retrieving_headers}
        return out

    @command('n')
    def getclaimtrie(self):
        """
        Return the entire claim trie
        """

        return self.network.synchronous_get(('blockchain.claimtrie.get', []))

    @command('n')
    def getclaimbyid(self, claim_id, raw=False):
        """
        Get claim by claim id
        """

        result = self.network.synchronous_get(('blockchain.claimtrie.getclaimbyid', [claim_id]))
        claims = format_amount_value(result)
        return self.parse_and_validate_claim_result(claims, raw=raw)

    @command('n')
    def getnthclaimforname(self, name, n, raw=False):
        """
        Get the last update to the nth claim to a name
        """

        result = self.network.synchronous_get(('blockchain.claimtrie.getnthclaimforname',
                                               [name, n]))
        claims = format_amount_value(result)
        return self.parse_and_validate_claim_result(claims, raw=raw)

    @command('w')
    def getnameclaims(self, raw=False, include_abandoned=False, include_supports=True,
                      claim_id=None, txid=None, nout=None):
        """
        Get  my name claims from wallet
        """

        result = self.wallet.get_name_claims(include_abandoned=include_abandoned,
                                             include_supports=include_supports)
        claims = format_amount_value(result)
        name_claims = []
        for claim in claims:
            parsed = self.parse_and_validate_claim_result(claim, raw=raw)
            if claim_id is not None and parsed['claim_id'] != claim_id:
                continue
            if txid is not None and nout is not None:

                if parsed['txid'] != txid or parsed['nout'] != nout:
                    continue
            name_claims.append(parsed)

        return name_claims

    @command('wpn')
    def getcertificateclaims(self, raw=False, include_abandoned=False):
        """
        Get my claims containing certificates
        """

        certificate_claims = []
        name_claims = self.wallet.get_name_claims(include_abandoned=include_abandoned,
                                                  include_supports=False)
        for claim in format_lbrycrd_keys(name_claims):
            try:
                decoded = smart_decode(claim['value'])
                if decoded.is_certificate:
                    cert_result = self.parse_and_validate_claim_result(claim, raw=raw)
                    if self.cansignwithcertificate(cert_result['claim_id']):
                        cert_result['can_sign'] = True
                    else:
                        cert_result['can_sign'] = False
                    certificate_claims.append(cert_result)
            except DecodeError:
                pass
        return format_amount_value(certificate_claims)

    def _calculate_fee(self, inputs, outputs, set_tx_fee):
        if set_tx_fee is not None:
            return set_tx_fee
        dummy_tx = Transaction.from_io(inputs, outputs)
        # fee per kb will default to RECOMMENDED_FEE, which is 50000
        # relay fee will default to 5000
        # fee is max(relay_fee, size is fee_per_kb * esimated_size)
        # will be roughly 10,000 deweys (0.0001 lbc), standard abandon should be about 200 bytes
        # this is assuming config is not set to dynamic, which in case it will get fees from
        # lbrycrds fee estimation algorithm

        size = dummy_tx.estimated_size()
        fee = Transaction.fee_for_size(self.wallet.relayfee(), self.wallet.fee_per_kb(self.config),
                                       size)
        return fee

    @command('w')
    def verify_claim_schema(self, val):
        """
        Parse an encoded claim value
        """

        try:
            decoded = smart_decode(val)
            results = {'claim_dictionary': decoded.claim_dict,
                       'serialized': decoded.serialized.encode('hex')}
            return results
        except DecodeError as err:
            return {'error': err}

    @command('wpn')
    def claim(self, name, val, amount, certificate_id=None, broadcast=True, claim_addr=None,
              tx_fee=None, change_addr=None, raw=False, skip_validate_schema=None,
              skip_update_check=None):
        """
        Claim a name
        """

        if skip_validate_schema and certificate_id:
            return {'success': False, 'reason': 'refusing to sign claim without validated schema'}

        parsed_claim = self.verify_request_to_make_claim(name, val, certificate_id)
        if 'error' in parsed_claim:
            return {'success': False, 'reason': parsed_claim['error']}

        parsed_uri = parse_lbry_uri(name)
        name = parsed_claim['name']
        val = parsed_claim['val']
        certificate_id = parsed_claim['certificate_id']

        if not skip_update_check:
            my_claims = [claim for claim in self.getnameclaims(include_supports=False) if
                         claim['name'] == name]
            if len(my_claims) > 1:
                return {'success': False, 'reason': "Dont know which claim to update"}
            if my_claims:
                my_claim = my_claims[0]

                if parsed_uri.claim_id and not my_claim['claim_id'].startswith(parsed_uri.claim_id):
                    return {'success': False,
                            'reason': 'claim id in URI does not match claim to update'}
                log.info("There is an unspent claim in your wallet for this name, updating "
                         "it instead")
                return self.update(name, val, amount=amount, broadcast=broadcast,
                                   claim_addr=claim_addr,
                                   tx_fee=tx_fee, change_addr=change_addr,
                                   certificate_id=certificate_id, raw=raw,
                                   skip_validate_schema=skip_validate_schema)
        if not raw:
            val = val.decode('hex')
        if claim_addr is None:
            claim_addr = self.wallet.create_new_address()
        if not base_decode(claim_addr, ADDRESS_LENGTH, 58):
            return {'error': 'invalid claim address'}

        if change_addr is None:
            change_addr = self.wallet.create_new_address(for_change=True)
        if not base_decode(change_addr, ADDRESS_LENGTH, 58):
            return {'error': 'invalid change address'}

        amount = int(COIN * amount)
        if amount <= 0:
            return {'success': False, 'reason': 'Amount must be greater than 0'}
        if tx_fee is not None:
            tx_fee = int(COIN * tx_fee)
            if tx_fee < 0:
                return {'success': False, 'reason': 'tx_fee must be greater than or equal to 0'}

        claim_value = None

        if not skip_validate_schema:
            try:
                claim_value = smart_decode(val)
            except DecodeError as err:
                return {'success': False,
                        'reason': 'Decode error: %s' % err}

            if not parsed_uri.is_channel and claim_value.is_certificate:
                return {'success': False,
                        'reason': 'Certificates must have URIs beginning with /"@/"'}

            if claim_value.has_signature:
                return {'success': False, 'reason': 'Claim value is already signed'}

            if certificate_id is not None:
                if not self.cansignwithcertificate(certificate_id):
                    return {'success': False,
                            'reason': 'Cannot sign for certificate %s' % certificate_id}

        if certificate_id and claim_value:
            signing_key = self.wallet.get_certificate_signing_key(certificate_id)
            signed = claim_value.sign(signing_key, claim_addr, certificate_id, curve=SECP256k1)
            val = signed.serialized

        outputs = [(TYPE_ADDRESS | TYPE_CLAIM, ((name, val), claim_addr), amount)]
        coins = self.wallet.get_spendable_coins()
        try:
            tx = self.wallet.make_unsigned_transaction(coins, outputs,
                                                       self.config, tx_fee, change_addr)
        except NotEnoughFunds:
            return {'success': False,
                    'reason': 'Not enough funds'}
        self.wallet.sign_transaction(tx, self._password)
        if broadcast:
            success, out = self.wallet.sendtx(tx)
            if not success:
                return {'success': False, 'reason': out}

        nout = None
        for i, output in enumerate(tx._outputs):
            if output[0] & TYPE_CLAIM:
                nout = i
        assert nout is not None

        claimid = encode_claim_id_hex(claim_id_hash(rev_hex(tx.hash()).decode('hex'), nout))
        return {"success": True, "txid": tx.hash(), "nout": nout, "tx": str(tx),
                "fee": str(Decimal(tx.get_fee()) / COIN), "claim_id": claimid}

    @command('wpn')
    def claimcertificate(self, name, amount, broadcast=True, claim_addr=None, tx_fee=None,
                         change_addr=None, set_default_certificate=None):
        """
        Generate a new signing key and make a certificate claim
        """

        if not parse_lbry_uri(name).is_channel:
            return {'error': 'non compliant uri for certificate'}
        secp256k1_private_key = get_signer(SECP256k1).generate().private_key.to_pem()
        claim = ClaimDict.generate_certificate(secp256k1_private_key, curve=SECP256k1)
        encoded_claim = claim.serialized.encode('hex')
        result = self.claim(name, encoded_claim, amount, broadcast=broadcast,
                            claim_addr=claim_addr, tx_fee=tx_fee, change_addr=change_addr)

        if result['success']:
            self.wallet.save_certificate(result['claim_id'], secp256k1_private_key)
            self.wallet.set_default_certificate(result['claim_id'],
                                                overwrite_existing=set_default_certificate)
        return result

    @command('wpn')
    def updateclaimsignature(self, name, amount=None, claim_id=None, certificate_id=None):
        """
        Update an unsigned claim with a signature
        """

        claim_value = None
        claim_address = None
        if claim_id is None:
            claims = self.getnameclaims(raw=True, include_supports=False)
            for claim in claims:
                if claim['name'] == name and not claim['is_spent']:
                    claim_id = claim['claim_id']
                    claim_value = claim['value']
                    claim_address = claim['address']
                    break

        if claim_id is None or claim_value is None:
            return {'error': 'no claim to update'}
        claim = smart_decode(claim_value)
        if certificate_id is None:
            certificate_id = claim.certificate_id
            certificate = self.getclaimbyid(certificate_id)
            if not certificate:
                raise Exception('Certificate claim {} not found'.format(claim.certificate_id))
        elif not self.cansignwithcertificate(certificate_id):
            return {
                'error': ('can update claim for lbry://{}#{}, but the signing key is '
                          'missing for certificate {}').format(name, claim_id, certificate_id)
            }
        else:
            certificate = self.getclaimbyid(str(certificate_id))
            if not certificate:
                raise Exception('Certificate claim {} not found'.format(claim.certificate_id))
        validated, channel_name = self.validate_claim_signature_and_get_channel_name(claim,
                                                                                     certificate,
                                                                                     claim_address)
        if validated:
            return {
                'error': 'lbry://{}#{} has a valid signature already'.format(name, claim_id)
            }

        return self.update(name, claim.serialized_no_signature, amount=amount,
                           certificate_id=certificate_id, claim_id=claim_id, raw=True)

    @command('wpn')
    def updatecertificate(self, name, amount=None, revoke=False, val=None):
        """
        Update a certificate claim
        """

        if not parse_lbry_uri(name).is_channel:
            return {'error': 'non compliant uri for certificate'}
        elif not revoke and not val:
            return {'error': 'nothing to update with'}

        if revoke:
            secp256k1_private_key = get_signer(SECP256k1).generate().private_key.to_pem()
            certificate = ClaimDict.generate_certificate(secp256k1_private_key, curve=SECP256k1)
            result = self.update(name, certificate.serialized, amount=amount, raw=True)
            self.wallet.save_certificate(result['claim_id'], secp256k1_private_key)
        else:
            decoded = smart_decode(val)
            if not decoded.is_certificate:
                return {'error': 'value is not a certificate'}
            result = self.update(name, decoded.serialized, amount=amount, raw=True)
        return result

    @command('wpn')
    def cansignwithcertificate(self, certificate_id):
        """
        Can sign with given claim certificate
        """

        if self.wallet.get_certificate_signing_key(certificate_id) is not None:
            return True
        return False

    @command('wpn')
    def support(self, name, claim_id, amount, broadcast=True, claim_addr=None, tx_fee=None,
                change_addr=None):
        """
        Support a name claim
        """

        if claim_addr is None:
            claim_addr = self.wallet.create_new_address()
        if change_addr is None:
            change_addr = self.wallet.create_new_address(for_change=True)

        claim_id = decode_claim_id_hex(claim_id)
        amount = int(COIN * amount)
        if amount <= 0:
            return {'success': False, 'reason': 'Amount must be greater than 0'}
        if tx_fee is not None:
            tx_fee = int(COIN * tx_fee)
            if tx_fee < 0:
                return {'success': False, 'reason': 'tx_fee must be greater than or equal to 0'}

        outputs = [(TYPE_ADDRESS | TYPE_SUPPORT, ((name, claim_id), claim_addr), amount)]
        coins = self.wallet.get_spendable_coins()
        try:
            tx = self.wallet.make_unsigned_transaction(coins, outputs, self.config, tx_fee,
                                                       change_addr)
        except NotEnoughFunds:
            return {'success': False, 'reason': 'Not enough funds'}
        self.wallet.sign_transaction(tx, self._password)
        if broadcast:
            success, out = self.wallet.sendtx(tx)
            if not success:
                return {'success': False, 'reason': out}

        nout = None
        for i, output in enumerate(tx._outputs):
            if output[0] & TYPE_SUPPORT:
                nout = i

        return {"success": True, "txid": tx.hash(), "nout": nout, "tx": str(tx),
                "fee": str(Decimal(tx.get_fee()) / COIN)}

    def verify_request_to_make_claim(self, uri, val, certificate_id):
        try:
            parsed_uri = parse_lbry_uri(uri)
        except URIParseError as err:
            return {'error': 'Failed to decode URI: %s' % err}

        if parsed_uri.is_channel:
            if parsed_uri.path:
                try:
                    if smart_decode(val).is_certificate:
                        return {'error': 'Claim in a channel should not contain a certificate'}
                except DecodeError as err:
                    return {'error': 'Failed to decode claim: %s' % err}
                name = parsed_uri.path
            else:
                try:
                    if not smart_decode(val).is_certificate:
                        return {'error': 'Channel claim does not contain a certificate'}
                except DecodeError as err:
                    return {'error': 'Failed to decode certificate in claim: %s' % err}
                name = parsed_uri.name
        else:
            name = parsed_uri.name

        return {'name': name, 'certificate_id': certificate_id, 'val': val}

    @command('wpn')
    def update(self, name, val, amount=None, certificate_id=None, claim_id=None, txid=None,
               nout=None, broadcast=True, claim_addr=None, tx_fee=None, change_addr=None, raw=None,
               skip_validate_schema=None):
        """
        Update a name claim
        """

        if skip_validate_schema and certificate_id:
            return {'success': False, 'reason': 'refusing to sign claim without validated schema'}

        parsed_claim = self.verify_request_to_make_claim(name, val, certificate_id)
        if 'error' in parsed_claim:
            return {'success': False, 'reason': parsed_claim['error']}

        parsed_uri = parse_lbry_uri(name)
        name = parsed_claim['name']
        val = parsed_claim['val']
        certificate_id = parsed_claim['certificate_id']

        if not raw:
            val = val.decode('hex')
        if not skip_validate_schema:
            try:
                decoded_claim = smart_decode(val)
            except DecodeError as err:
                return {'success': False, 'reason': 'Decode error: %s' % err}
        else:
            decoded_claim = None
        if claim_addr is None:
            claim_addr = self.wallet.create_new_address()
        if not base_decode(claim_addr, ADDRESS_LENGTH, 58):
            return {'error': 'invalid claim address'}

        if change_addr is None:
            change_addr = self.wallet.create_new_address(for_change=True)
        if claim_id is None or txid is None or nout is None:
            claims = self.getnameclaims()
            for claim in claims:
                if claim['name'] == name and not claim['is_spent']:
                    claim_id = claim['claim_id']
                    txid = claim['txid']
                    nout = claim['nout']
                    break
            if not claim_id:
                return {'success': False, 'reason': 'No claim to update'}

        if not skip_validate_schema:
            try:
                claim_value = smart_decode(val)
            except DecodeError as err:
                return {'success': False,
                        'reason': 'Decode error: %s' % err}

            if not parsed_uri.is_channel and claim_value.is_certificate:
                return {'success': False,
                        'reason': 'Certificates must have URIs beginning with /"@/"'}

            if claim_value.has_signature:
                return {'success': False, 'reason': 'Claim value is already signed'}

            if certificate_id is not None:
                if not self.cansignwithcertificate(certificate_id):
                    return {'success': False,
                            'reason': 'Cannot sign for certificate %s' % certificate_id}

            if certificate_id and claim_value:
                signing_key = self.wallet.get_certificate_signing_key(certificate_id)
                signed = claim_value.sign(signing_key, claim_addr, certificate_id, curve=SECP256k1)
                val = signed.serialized

            if certificate_id and decoded_claim:
                signing_key = self.wallet.get_certificate_signing_key(certificate_id)
                if signing_key:
                    signed = decoded_claim.sign(signing_key,
                                                claim_addr,
                                                certificate_id,
                                                curve=SECP256k1)
                    val = signed.serialized
                else:
                    return {'success': False,
                            'reason': "Cannot sign with certificate %s" % certificate_id}

            elif not certificate_id and decoded_claim:
                if decoded_claim.has_signature:
                    certificate_id = decoded_claim.certificate_id
                    signing_key = self.wallet.get_certificate_signing_key(certificate_id)
                    if signing_key:
                        claim = ClaimDict.deserialize(val)
                        signed = claim.sign(signing_key,
                                            claim_addr,
                                            certificate_id,
                                            curve=SECP256k1)
                        val = signed.serialized
                    else:
                        return {'success': False,
                                'reason': "Cannot sign with certificate %s" % certificate_id}

        decoded_claim_id = decode_claim_id_hex(claim_id)

        if amount is not None:
            amount = int(COIN * amount)
            if amount <= 0:
                return {'success': False, 'reason': 'Amount must be greater than 0'}
        if tx_fee is not None:
            tx_fee = int(COIN * tx_fee)
            if tx_fee < 0:
                return {'success': False, 'reason': 'tx_fee must be greater than or equal to 0'}

        claim_utxo = self.wallet.get_spendable_claimtrietx_coin(txid, nout)
        if claim_utxo['is_support']:
            return {'success': False, 'reason': 'Cannot update a support'}

        inputs = [claim_utxo]
        txout_value = claim_utxo['value']

        # if amount is not specified, keep the same amount minus the tx fee
        if amount is None:
            dummy_outputs = [
                (
                    TYPE_ADDRESS | TYPE_UPDATE,
                    ((name, decoded_claim_id, val), claim_addr),
                    txout_value
                )
            ]
            fee = self._calculate_fee(inputs, dummy_outputs, tx_fee)
            if fee >= txout_value:
                return {
                    'success': False,
                    'reason': 'Fee will exceed amount available in original bid. Increase amount'
                }

            outputs = [
                (
                    TYPE_ADDRESS | TYPE_UPDATE,
                    ((name, decoded_claim_id, val), claim_addr),
                    txout_value - fee
                )
            ]

        elif amount <= 0:
            return {'success': False, 'reason': 'Amount must be greater than zero'}

        # amount is more than the original bid or equal, we need to get an input
        elif amount >= txout_value:
            additional_input_fee = 0
            if tx_fee is None:
                claim_input_size = Transaction.estimated_input_size(claim_utxo)
                additional_input_fee = Transaction.fee_for_size(self.wallet.relayfee(),
                                                                self.wallet.fee_per_kb(self.config),
                                                                claim_input_size)

            get_inputs_for_amount = amount - txout_value + additional_input_fee
            # create a dummy tx for the extra amount in order to get the proper inputs to spend
            dummy_outputs = [
                (
                    TYPE_ADDRESS | TYPE_UPDATE,
                    ((name, decoded_claim_id, val), claim_addr),
                    get_inputs_for_amount
                )
            ]
            coins = self.wallet.get_spendable_coins()
            try:
                dummy_tx = self.wallet.make_unsigned_transaction(coins, dummy_outputs,
                                                                 self.config, tx_fee, change_addr)
            except NotEnoughFunds:
                return {'success': False, 'reason': 'Not enough funds'}

            # add the unspents to input
            for i in dummy_tx._inputs:
                inputs.append(i)

            outputs = [
                (
                    TYPE_ADDRESS | TYPE_UPDATE,
                    ((name, decoded_claim_id, val), claim_addr),
                    amount
                )
            ]
            # add the change utxos to output
            for output in dummy_tx._outputs:
                if not output[0] & TYPE_UPDATE:
                    outputs.append(output)

        # amount is less than the original bid,
        # we need to put remainder minus fees in a change address
        elif amount < txout_value:

            dummy_outputs = [
                (
                    TYPE_ADDRESS | TYPE_UPDATE,
                    ((name, decoded_claim_id, val), claim_addr),
                    amount
                ),
                (
                    TYPE_ADDRESS,
                    change_addr,
                    txout_value - amount
                )
            ]
            fee = self._calculate_fee(inputs, dummy_outputs, tx_fee)
            if fee > txout_value - amount:
                return {
                    'success': False,
                    'reason': 'Fee will be greater than change amount, use amount=None to expend '
                              'change as fee'
                }

            outputs = [
                (
                    TYPE_ADDRESS | TYPE_UPDATE,
                    ((name, decoded_claim_id, val), claim_addr),
                    amount
                ),
                (
                    TYPE_ADDRESS,
                    change_addr,
                    txout_value - amount - fee
                )
            ]

        tx = Transaction.from_io(inputs, outputs)
        self.wallet.sign_transaction(tx, self._password)
        if broadcast:
            success, out = self.wallet.sendtx(tx)
            if not success:
                return {"success": False, "reason": out}

        nout = None
        amount = 0
        for i, output in enumerate(tx._outputs):
            if output[0] & TYPE_UPDATE:
                nout = i
                amount = output[2]

        return {
            "success": True,
            "txid": tx.hash(),
            "nout": nout,
            "tx": str(tx),
            "fee": str(Decimal(tx.get_fee()) / COIN),
            "amount": str(Decimal(amount) / COIN),
            "claim_id": claim_id
        }

    @command('wpn')
    def abandon(self, claim_id=None, txid=None, nout=None, broadcast=True, return_addr=None,
                tx_fee=None):
        """
        Abandon a name claim

        Either specify the claim with a claim_id or with txid and nout
        """
        claims = self.getnameclaims(raw=True, include_abandoned=False, include_supports=True,
                                    claim_id=claim_id, txid=txid, nout=nout)
        if len(claims) > 1:
            return {"success": False, 'reason': 'more than one claim that matches'}
        elif len(claims) == 0:
            return {"success": False, 'reason': 'claim not found', 'claim_id': claim_id}
        else:
            claim = claims[0]

        txid, nout = claim['txid'], claim['nout']
        if return_addr is None:
            return_addr = self.wallet.create_new_address()
        if tx_fee is not None:
            tx_fee = int(COIN * tx_fee)
            if tx_fee < 0:
                return {'success': False, 'reason': 'tx_fee must be greater than or equal to 0'}

        i = self.wallet.get_spendable_claimtrietx_coin(txid, nout)
        inputs = [i]
        txout_value = i['value']
        # create outputs
        outputs = [(TYPE_ADDRESS, return_addr, txout_value)]
        # fee will be roughly 10,000 deweys (0.0001 lbc), standard abandon should be about 200 bytes
        # this is assuming config is not set to dynamic, which in case it will get fees from
        # lbrycrd's fee estimation algorithm

        fee = self._calculate_fee(inputs, outputs, tx_fee)
        if fee > txout_value:
            return {'success': False, 'reason': 'transaction fee exceeds amount to abandon'}
        return_value = txout_value - fee

        # create transaction
        outputs = [(TYPE_ADDRESS, return_addr, return_value)]
        tx = Transaction.from_io(inputs, outputs)
        self.wallet.sign_transaction(tx, self._password)
        if broadcast:
            success, out = self.wallet.sendtx(tx)
            if not success:
                return {'success': False, 'reason': out}
        return {'success': True, 'txid': tx.hash(), 'tx': str(tx),
                'fee': str(Decimal(tx.get_fee()) / COIN)}


param_descriptions = {
    'privkey': 'Private key. Type \'?\' to get a prompt.',
    'destination': 'Bitcoin address, contact or alias',
    'address': 'Bitcoin address',
    'seed': 'Seed phrase',
    'txid': 'Transaction ID',
    'pos': 'Position',
    'height': 'Block height',
    'tx': 'Serialized transaction (hexadecimal)',
    'key': 'Variable name',
    'pubkey': 'Public key',
    'message': 'Clear text message. Use quotes if it contains spaces.',
    'encrypted': 'Encrypted message',
    'amount': 'Amount to be sent (in BTC). Type \'!\' to send the maximum available.',
    'requested_amount': 'Requested amount (in BTC).',
    'outputs': 'list of ["address", amount]',
    'exclude_claimtrietx': 'Exclude claimtrie transactions.',
    'set_default_certificate': 'Set new certificate as default signer even if there is already a '
                               'default certificate',
}

command_options = {
    'password': ("-W", "--password", "Password"),
    'receiving': (None, "--receiving", "Show only receiving addresses"),
    'change': (None, "--change", "Show only change addresses"),
    'frozen': (None, "--frozen", "Show only frozen addresses"),
    'unused': (None, "--unused", "Show only unused addresses"),
    'funded': (None, "--funded", "Show only funded addresses"),
    'show_balance': ("-b", "--balance", "Show the balances of listed addresses"),
    'show_labels': ("-l", "--labels", "Show the labels of listed addresses"),
    'nocheck': (None, "--nocheck", "Do not verify aliases"),
    'tx_fee': ("-f", "--fee", "Transaction fee (in BTC)"),
    'from_addr': ("-F", "--from",
                  "Source address. If it isn't in the wallet, it will ask for the private key "
                  "unless supplied in the format public_key:private_key. It's not saved in the "
                  "wallet."),
    'change_addr': ("-c", "--change",
                    "Change address. Default is a spare address, or the source address if it's "
                    "not in the wallet"),
    'nbits': (None, "--nbits", "Number of bits of entropy"),
    'entropy': (None, "--entropy", "Custom entropy"),
    'language': ("-L", "--lang", "Default language for wordlist"),
    'gap_limit': ("-G", "--gap", "Gap limit"),
    'privkey': (None, "--privkey", "Private key. Set to '?' to get a prompt."),
    'unsigned': ("-u", "--unsigned", "Do not sign transaction"),
    'domain': ("-D", "--domain", "List of addresses"),
    'account': (None, "--account", "Account"),
    'memo': ("-m", "--memo", "Description of the request"),
    'expiration': (None, "--expiration", "Time in seconds"),
    'force': (None, "--force", "Create new address beyong gap limit, if no more address is "
                               "available."),
    'pending': (None, "--pending", "Show only pending requests."),
    'expired': (None, "--expired", "Show only expired requests."),
    'paid': (None, "--paid", "Show only paid requests."),
    'exclude_claimtrietx': (None, "--exclude_claimtrietx", "Exclude claimtrie transactions"),
    'return_addr': (None, "--return_addr",
                    "Return address where amounts in abandoned claimtrie transactions are "
                    "returned."),
    'claim_addr': (None, "--claim_addr", "Address where claims are sent."),
    'broadcast': (None, "--broadcast", "if True, broadcast the transaction"),
    'raw': ("-r", "--raw", "if True, don't decode claim values"),
    'page': ("-p", "--page", "page number"),
    'page_size': ("-s", "--page_size", "page size"),
    'claim_id': (None, "--claim_id", "claim id"),
    'txid': ("-t", "--txid", "txid"),
    'nout': ("-n", "--nout", "nout"),
    'certificate_id': (None, "--certificate_id", "claim id of a certificate that can be used "
                                                 "for signing"),
    'skip_validate_schema': (None, "--ignore_schema", "Validate the claim conforms with lbry "
                                                      "schema"),
    'set_default_certificate': (None, "--set_default_certificate",
                                "Set the new certificate as the default, even if there already is "
                                "one"),
    'amount': ("-a", "--amount", "amount to use in updated name claim"),
    'include_abandoned': (None, "--include_abandoned", "include abandoned claims"),
    'include_supports': (None, "--include_supports", "include supports"),
    'skip_update_check': (None, "--skip_update_check",
                          "do not check for an existing unspent claim before making a new one"),
    'revoke': (None, "--revoke", "if true, create a new signing key and revoke the old one"),
    'val': (None, '--value', 'claim value'),
    'timeout': (None, '--timeout', 'timeout')
}


def json_loads(x):
    """don't use floats because of rounding errors"""
    return json.loads(x, parse_float=lambda x: str(Decimal(x)))


arg_types = {
    'num': int,
    'nbits': int,
    'entropy': long,
    'tx': json_loads,
    'pubkeys': json_loads,
    'inputs': json_loads,
    'outputs': json_loads,
    'tx_fee': lambda x: str(Decimal(x)) if x is not None else None,
    'amount': lambda x: str(Decimal(x)) if x != '!' else '!',
}

config_variables = {

    'addrequest': {
        'requests_dir': 'directory where a bip70 file will be written.',
        'ssl_privkey': 'Path to your SSL private key, needed to sign the request.',
        'ssl_chain': 'Chain of SSL certificates, needed for signed requests. Put your certificate '
                     'at the top and the root CA at the end',
        'url_rewrite': 'Parameters passed to str.replace(), in order to create the r= part of '
                       'bitcoin: URIs. Example: \"(\'file:///var/www/\',\'https://lbryum.org/\')\"',
    },
    'listrequests': {
        'url_rewrite': 'Parameters passed to str.replace(), in order to create the r= part of '
                       'bitcoin: URIs. Example: \"(\'file:///var/www/\',\'https://lbryum.org/\')\"',
    }
}


def set_default_subparser(self, name, args=None):
    """
    see http://stackoverflow.com/questions/5176691/argparse-how-to-specify-a-default-subcommand
    """

    subparser_found = False
    for arg in sys.argv[1:]:
        if arg in ['-h', '--help']:  # global help if no subparser
            break
    else:
        for x in self._subparsers._actions:
            if not isinstance(x, argparse._SubParsersAction):
                continue
            for sp_name in x._name_parser_map.keys():
                if sp_name in sys.argv[1:]:
                    subparser_found = True
        if not subparser_found:
            # insert default in first position, this implies no
            # global options without a sub_parsers specified
            if args is None:
                sys.argv.insert(1, name)
            else:
                args.insert(0, name)


argparse.ArgumentParser.set_default_subparser = set_default_subparser


def add_network_options(parser):
    parser.add_argument("-1", "--oneserver", action="store_true", dest="oneserver", default=False,
                        help="connect to one server only")
    parser.add_argument("-s", "--server", dest="server", default=None,
                        help="set server host:port:protocol, where protocol is either t (tcp) or"
                             " s (ssl)")
    parser.add_argument("-p", "--proxy", dest="proxy", default=None,
                        help="set proxy [type:]host[:port], where type is socks4,socks5 or http")


def get_parser():
    # parent parser, because set_default_subparser removes global options
    parent_parser = argparse.ArgumentParser('parent', add_help=False)
    group = parent_parser.add_argument_group('global options')
    group.add_argument("-v", "--verbose", action="store_true", dest="verbose", default=False,
                       help="Show debugging information")
    group.add_argument("-P", "--portable", action="store_true", dest="portable", default=False,
                       help="Use local 'electrum_data' directory")
    group.add_argument("-w", "--wallet", dest="wallet_path", help="wallet path")
    group.add_argument("-D", "--dir", dest="lbryum_path", help="electrum directory")
    # create main parser
    parser = argparse.ArgumentParser(
        parents=[parent_parser],
        epilog="Run 'lbryum help <command>' to see the help for a command")
    subparsers = parser.add_subparsers(dest='cmd', metavar='<command>')
    # daemon
    parser_daemon = subparsers.add_parser('daemon', parents=[parent_parser], help="Run Daemon")
    parser_daemon.add_argument("subcommand", choices=['start', 'status', 'stop'])
    # parser_daemon.set_defaults(func=run_daemon)
    add_network_options(parser_daemon)
    # commands
    for cmdname in sorted(Commands.known_commands.keys()):
        cmd = Commands.known_commands[cmdname]
        p = subparsers.add_parser(cmdname, parents=[parent_parser], help=cmd.help,
                                  description=cmd.description)
        # p.set_defaults(func=run_cmdline)
        if cmd.requires_password:
            p.add_argument("-W", "--password", dest="password", default=None, help="password")
        for optname, default in zip(cmd.options, cmd.defaults):
            a, b, help = command_options[optname]
            action = "store_true" if type(default) is bool else 'store'
            args = (a, b) if a else (b,)
            if action == 'store':
                _type = arg_types.get(optname, str)
                p.add_argument(*args, dest=optname, action=action, default=default, help=help,
                               type=_type)
            else:
                p.add_argument(*args, dest=optname, action=action, default=default, help=help)

        for param in cmd.params:
            h = param_descriptions.get(param, '')
            _type = arg_types.get(param, str)
            p.add_argument(param, help=h, type=_type)

        cvh = config_variables.get(cmdname)
        if cvh:
            group = p.add_argument_group('configuration variables',
                                         '(set with setconfig/getconfig)')
            for k, v in cvh.items():
                group.add_argument(k, nargs='?', help=v)

    # 'cmd' is the default command
    parser.set_default_subparser('cmd')
    return parser
