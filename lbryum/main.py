import json
import logging
import os
import sys
import getpass
import requests  # TODO: use txrequests

from lbryum.commands import Commands, config_variables, get_parser
from lbryum.daemon import Daemon, get_daemon
from lbryum.network import Network, SimpleConfig
from lbryum.util import json_decode
from lbryum.errors import InvalidPassword
from lbryum.wallet import Wallet, WalletStorage

log = logging.getLogger(__name__)


# get password routine
def prompt_password(prompt, confirm=True):
    password = getpass.getpass(prompt, stream=None)
    if password and confirm:
        password2 = getpass.getpass("Confirm: ")
        if password != password2:
            sys.exit("Error: Passwords do not match.")
    if not password:
        password = None
    return password


def run_non_RPC(config):
    cmdname = config.get('cmd')

    storage = WalletStorage(config.get_wallet_path())
    if storage.file_exists:
        sys.exit("Error: Remove the existing wallet first!")

    def password_dialog():
        return prompt_password("Password (hit return if you do not wish to encrypt your wallet):")

    if cmdname == 'restore':
        text = config.get('text')
        password = password_dialog() if Wallet.is_seed(text) or Wallet.is_xprv(
            text) or Wallet.is_private_key(text) else None
        try:
            wallet = Wallet.from_text(text, password, storage)
        except BaseException as e:
            sys.exit(str(e))
        if not config.get('offline'):
            network = Network(config)
            network.start()
            wallet.start_threads(network)
            log.info("Recovering wallet...")
            wallet.synchronize()
            wallet.wait_until_synchronized()
            msg = "Recovery successful" if wallet.is_found() else "Found no history for this wallet"
        else:
            msg = "This wallet was restored offline. It may contain more addresses than displayed."
        log.info(msg)
    elif cmdname == 'create':
        password = password_dialog()
        wallet = Wallet(storage)
        seed = wallet.make_seed()
        wallet.add_seed(seed, password)
        wallet.create_master_keys(password)
        wallet.create_main_account()
        wallet.synchronize()
        print "Your wallet generation seed is:\n\"%s\"" % seed
        print "Please keep it in a safe place; if you lose it, you will not be able to restore " \
              "your wallet."
    elif cmdname == 'deseed':
        wallet = Wallet(storage)
        if not wallet.seed:
            log.info("Error: This wallet has no seed")
        else:
            ns = wallet.storage.path + '.seedless'
            print "Warning: you are going to create a seedless wallet'\n" \
                  "It will be saved in '%s'" % ns
            if raw_input("Are you sure you want to continue? (y/n) ") in ['y', 'Y', 'yes']:
                wallet.storage.path = ns
                wallet.seed = ''
                wallet.storage.put('seed', '')
                wallet.use_encryption = False
                wallet.storage.put('use_encryption', wallet.use_encryption)
                for k in wallet.imported_keys.keys():
                    wallet.imported_keys[k] = ''
                wallet.storage.put('imported_keys', wallet.imported_keys)
                print "Done."
            else:
                print "Action canceled."
        wallet.storage.write()
    else:
        raise Exception("Unknown command %s" % cmdname)
    wallet.storage.write()
    log.info("Wallet saved in '%s'", wallet.storage.path)


def init_cmdline(config_options):
    config = SimpleConfig(config_options)
    cmdname = config.get('cmd')
    cmd = Commands.known_commands[cmdname]

    # instanciate wallet for command-line
    storage = WalletStorage(config.get_wallet_path())

    if cmd.requires_wallet and not storage.file_exists:
        log.error("Error: Wallet file not found.")
        print "Type 'lbryum create' to create a new wallet, or provide a path to a wallet with " \
              "the -w option"
        sys.exit(0)

    # important warning
    if cmd.name in ['getprivatekeys']:
        print "WARNING: ALL your private keys are secret."
        print "Exposing a single private key can compromise your entire wallet!"
        print "In particular, DO NOT use 'redeem private key' services proposed by third parties."

    # commands needing password
    if cmd.requires_password and storage.get('use_encryption'):
        if config.get('password'):
            password = config.get('password')
        else:
            password = prompt_password('Password:', False)
            if not password:
                print "Error: Password required"
                sys.exit(1)
            Wallet(storage).check_password(password)
    else:
        password = None

    config_options['password'] = password

    if cmd.name == 'password':
        new_password = prompt_password('New password:')
        config_options['password'] = password
        config_options['new_password'] = new_password

    return cmd, password


def run_offline_command(config, config_options):
    cmdname = config.get('cmd')
    cmd = Commands.known_commands[cmdname]
    storage = WalletStorage(config.get_wallet_path())
    wallet = Wallet(storage) if cmd.requires_wallet else None
    # check password
    if cmd.requires_password and storage.get('use_encryption'):
        password = config_options.get('password')
        try:
            seed = wallet.check_password(password)
        except InvalidPassword:
            print "Error: This password does not decode this wallet."
            sys.exit(1)
    if cmd.requires_network:
        print "Warning: running command offline"
    # arguments passed to function
    args = map(lambda x: config.get(x), cmd.params)
    # decode json arguments
    args = map(json_decode, args)
    # options
    args += map(lambda x: config.get(x), cmd.options)
    cmd_runner = Commands(config, wallet, None,
                          password=config_options.get('password'),
                          new_password=config_options.get('new_password'))
    func = getattr(cmd_runner, cmd.name)
    result = func(*args)
    # save wallet
    if wallet:
        wallet.storage.write()
    return result


def main():
    # make sure that certificates are here
    assert os.path.exists(requests.utils.DEFAULT_CA_BUNDLE_PATH)

    # parse command line
    parser = get_parser()
    args = parser.parse_args()

    if args.verbose:
        logging.getLogger("lbryum").setLevel(logging.INFO)
    else:
        logging.getLogger("lbryum").setLevel(logging.ERROR)

    # config is an object passed to the various constructors (wallet, interface)
    config_options = args.__dict__
    for k, v in config_options.items():
        if v is None or (k in config_variables.get(args.cmd, {}).keys()):
            config_options.pop(k)
    if config_options.get('server'):
        config_options['auto_connect'] = False
    config = SimpleConfig(config_options)
    cmdname = config.get('cmd')

    # run non-RPC commands separately
    if cmdname in ['create', 'restore', 'deseed']:
        run_non_RPC(config)
        sys.exit(0)

    # check if a daemon is running
    server = get_daemon(config)

    if cmdname == 'daemon':
        if server is not None:
            result = server.daemon(config_options)
        else:
            subcommand = config.get('subcommand')
            if subcommand in ['status', 'stop']:
                print "Daemon not running"
                sys.exit(1)
            elif subcommand == 'start':
                if hasattr(os, "fork"):
                    p = os.fork()
                else:
                    log.warning("Cannot start lbryum daemon as a background process")
                    log.warning("To use lbryum commands, run them from a different window")
                    p = 0
                if p == 0:
                    network = Network(config)
                    network.start()
                    daemon = Daemon(config, network)
                    daemon.start()
                    daemon.join()
                    sys.exit(0)
                else:
                    print "starting daemon (PID %d)" % p
                    sys.exit(0)
            else:
                print "syntax: lbryum daemon <start|status|stop>"
                sys.exit(1)
    else:
        # command line
        init_cmdline(config_options)
        if server is not None:
            result = server.run_cmdline(config_options)
        else:
            cmd = Commands.known_commands[cmdname]
            if cmd.requires_network:
                print "Network daemon is not running. Try 'lbryum daemon start'"
                sys.exit(1)
            else:
                result = run_offline_command(config, config_options)
    print json.dumps(result, indent=2)
    sys.exit(0)


if __name__ == '__main__':
    main()
