import logging

log = logging.getLogger("lbryum")

DEFAULT_FORMAT = "%(asctime)s %(levelname)-8s %(name)s:%(lineno)d: %(message)s"

handler = logging.NullHandler()
handler.setFormatter(logging.Formatter(DEFAULT_FORMAT))
log.addHandler(handler)
log.setLevel(logging.INFO)

__version__ = "3.1.4rc3"
