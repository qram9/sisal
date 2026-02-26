def types_sisal():
    print("let basic_type_list =")

def type_triplet(alis):
    print("let basic_types = [" + " ; ".join([f"({ty}, {cou})" for cou,
                                           ty in alis]) + "]")
    print("and lookup_tyid_triple = function " + " | ".join([f"{ty} -> ({cou}, 0, {cou})" for cou,
                                           ty in alis]))


def mangle_it ():
    basic_types = []
    dic = {'BOOLEAN':'B', 'CHARACTER':'C', 'DOUBLE':'D',
           'INTEGRAL':'I',
           'REAL':'F',
           'BYTE':'Y', 'UCHAR': 'UC', 'HALF':'H', 'SHORT':'S',
           'USHORT':'US',
           'UINT':'UI',  'UBYTE' :'UY', 'LONG' : 'L', 'ULONG' : 'UL'}
    cou = 1
    basic_types.append((cou, "BOOLEAN"))
    cou = 2
    for v in (None, "2", "3", "4", "8", "16"):
        for ty in sorted([ "CHARACTER", "DOUBLE", "INTEGRAL", "REAL",
               "BYTE", "UCHAR", "HALF", "SHORT", "USHORT", "UINT",  "UBYTE",
               "ULONG", "LONG"]):
            if v is None:
                basic_types.append((cou , ty))
            else:
                basic_types.append((cou, ty+v))
            cou+=1
    basic_types.append((cou, "MAT2"))
    cou+=1
    basic_types.append((cou, "MAT3"))
    cou+=1
    basic_types.append((cou, "MAT4"))
    cou+=1
    print("and lookup_tyid = function " + " | ".join([f"{ty} -> {cou}" for cou, ty in basic_types]))
    print("and rev_lookup_ty_name = function " + " | ".join([f'{cou} -> "{ty}"' for cou, ty in basic_types]))
    print("and lookup_tyid_triple = function " + " | ".join([f"{ty} -> ({cou}, 0, {cou})" for cou, ty in basic_types]))
    for ty in sorted([ "NULL", "ARRAY", "STREAM", "RECORD","UNION"]):
        basic_types.append((cou , ty))
        cou+=1
    print("let basic_types =", "; ".join([f'({cou}, {ty})' for cou, ty in basic_types]))
    cou = 2
    mangle = []
    for v in (None, "2", "3", "4", "8", "16"):
        for ty in sorted(["CHARACTER", "DOUBLE", "INTEGRAL", "REAL",
               "BYTE", "UCHAR", "HALF", "SHORT", "USHORT", "UINT",  "UBYTE",
               "ULONG", "LONG"]):
            if v is None:
                mangle.append(f'| {cou} -> "{dic[ty]}"')
            else:
                mangle.append(f'| {cou}  -> "V{v}{dic[ty]}"')
            cou+=1
    mangle.append(f' | {cou} -> "M2" | {cou + 1} -> "M3" | {cou + 2} -> "M4"')
    print("and short_name_for_intrinsic = function ", " ".join(mangle))

def type_id():
    #print("let basic_types = [")
    cou = 1
    alis = []

    for k in ["", 2, 3, 4, 8, 16]:
        for ty in sorted([ "CHAR", "DOUBLE", "INT", "FLOAT", "LONG", "ULONG",
                   "BYTE", "UCHAR", "HALF", "SHORT", "USHORT", "UINT",
                   "UBYTE",]):
            alis.append((cou, ty+str(k)))
            cou+=1
    for ty in sorted([ "NULL", "ARRAY", "STREAM", "RECORD","UNION"]):
        alis.append((cou, ty))
        cou+=1
    print("and lookup_tyid = function " + " | ".join([f"{ty} -> {cou}" for cou,
                                           ty in alis]))
    return alis

if __name__ == '__main__':
    mangle_it()
