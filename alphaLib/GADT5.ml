type atom

type ('p, 'data) xdesc =
| XDescUnit: ('p, unit) xdesc
| XDescPair: ('p, 'a) xdesc * ('p, 'b) xdesc -> ('p, 'a * 'b) xdesc
| XDescUniv: ('p, 'a) xdesc
| XDescAtom: ('p, atom) xdesc
| XDescAbs : ('p, 'p) xdesc

