import re

import lbrycrd
from util import StoreDict


class Contacts(StoreDict):
    def __init__(self, config):
        StoreDict.__init__(self, config, 'contacts')

    def resolve(self, k):
        if lbrycrd.is_address(k):
            return {
                'address': k,
                'type': 'address'
            }
        if k in self.keys():
            _type, addr = self[k]
            if _type == 'address':
                return {
                    'address': addr,
                    'type': 'contact'
                }
        raise Exception("Invalid Bitcoin address or alias", k)

    def find_regex(self, haystack, needle):
        regex = re.compile(needle)
        try:
            return regex.search(haystack).groups()[0]
        except AttributeError:
            return None