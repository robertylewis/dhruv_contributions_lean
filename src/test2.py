import requests
import urllib.parse
import json
import sys

sage_functions = '''
from sage.structure.sequence import Sequence
import numpy as np

# dictionary handling
def one_hot(i,n):
    out = [0 for _ in range(n)]
    out[i] = 1
    return out

# some aliases that conform to Becker and Weispfenning's notation:
LCM = lambda f, g: f.parent().monomial_lcm(f, g)
LM = lambda f: f.lm()
LT = lambda f: f.lt()

def spol(f, g, gen_dict):
    fg_lcm = LCM(LM(f), LM(g))
    sp = fg_lcm//LT(f)*f - fg_lcm//LT(g)*g
    n = len(gen_dict[f])
    gen_dict[sp] = [fg_lcm//LT(f) * gen_dict[f][j] - fg_lcm//LT(g) * gen_dict[g][j] for j in range(n)]
    return fg_lcm//LT(f)*f - fg_lcm//LT(g)*g

def select(P):
    return min(P, key=lambda fi_fj: LCM(LM(fi_fj[0]),
                                        LM(fi_fj[1])).total_degree())
def multi_div(f, polys):
    n = len(polys)
    quot = [0 for _ in range(n)]
    r = 0
    
    p = f
    while p != 0:
        i = 0
        division_occured = False
        
        while i < n and not division_occured:
            try:
                sub_q, sub_r = LT(p).quo_rem(LT(polys[i]))
            except:
                i += 1
            else:
                if sub_r == 0:
                    quot[i] += sub_q
                    p -= sub_q * polys[i]
                    division_occured = True
                else:
                    i += 1
        if division_occured == False:
            r += LT(p)
            p -= LT(p)
    return quot, r

def reduce_and_record(p, polys, gen_dict, add_back = False): # only works if gen_dict knows about p and polys
    #TODO - maybe remove p from gen_dict here, because It won't get used again I don't think
    quot, r = multi_div(p, polys)
    if r != 0:
        if add_back:
            polys.append(r)
        p_vector = gen_dict[p]
        gen_coeffs_for_quot = [sum([gen_dict[polys[i]][j] * quot[i] for i in range(len(quot))]) for j in range(len(p_vector))]
        gen_dict[r] = [p_vector[j] - gen_coeffs_for_quot[j] for j in range(len(p_vector))]
    return r, polys

def inter_reduction(polys, gen_dict):
    if len(polys) == 0:
        return polys  # if polys is empty we cannot get a base ring
    base_ring = polys[0].base_ring()

    while True:
        poly_bar = polys.copy()
        for p in poly_bar:
            polys.remove(p)
            _ = reduce_and_record(p, polys, gen_dict, add_back=True)
        if set(poly_bar) == set(polys):
            if base_ring.is_field():
                out = [0 for _ in range(len(polys))]
                for i in range(len(polys)):
                    out[i] = polys[i].lc() ** (-1) * polys[i]
                    gen_dict[out[i]] = [polys[i].lc() ** (-1) * gen_dict[polys[i]][j] for j in range(len(gen_dict[polys[i]]))]
                return out
            else:
                return poly_bar

def update(G, B, h):
    R = h.parent()

    C = set((h, g) for g in G)
    D = set()

    while C:
        (h, g) = C.pop()

        lcm_divides = lambda rhs: R.monomial_divides(LCM(LM(h), LM(rhs[1])),
                                                     LCM(LM(h), LM(g)))

        if R.monomial_pairwise_prime(LM(h), LM(g)) or \
                (
                   not any(lcm_divides(f) for f in C)
                   and
                   not any(lcm_divides(f) for f in D)
                ):
            D.add((h, g))

    E = set()

    while D:
        (h, g) = D.pop()
        if not R.monomial_pairwise_prime(LM(h), LM(g)):
            E.add((h, g))

    B_new = set()

    while B:
        g1, g2 = B.pop()
        if not R.monomial_divides(LM(h), LCM(LM(g1), LM(g2))) or \
           R.monomial_lcm(LM(g1), LM(h)) == LCM(LM(g1), LM(g2)) or \
           R.monomial_lcm(LM(h), LM(g2)) == LCM(LM(g1), LM(g2)):
            B_new.add((g1, g2))

    B_new = B_new.union(E)

    G_new = set()

    while G:
        g = G.pop()
        if not R.monomial_divides(LM(h), LM(g)):
            G_new.add(g)

    G_new.add(h)

    return G_new, B_new

def buchberger_improved(gens):
    n = len(gens)
    gen_dict = {gens[i] : one_hot(i, n) for i in range(n)}
    F = inter_reduction(gens, gen_dict)

    G = set()
    B = set()

    while len(F) > 0:
        f = min(F)
        F.remove(f)
        G, B = update(G, B, f)

    while B:
        g1, g2 = select(B)
        B.remove((g1, g2))
        sp = spol(g1, g2, gen_dict)
        h, _ = reduce_and_record(sp, list(G), gen_dict)
        if h != 0:
            G, B = update(G, B, h)

    return inter_reduction(list(G), gen_dict), gen_dict

def grob_to_matrix(basis, gen_dict):
    A = []
    for g in basis:
        A.append(gen_dict[g])
    return A

def ideal_membership(p, gens):
    basis, gen_dict = buchberger_improved(gens)
    n = len(basis)

    quot, r = multi_div(p, basis)
    A = np.array(grob_to_matrix(basis, gen_dict))
    b = np.array(quot).reshape((1,n))

    return basis, np.matmul(b,A), r

def const_string(const):
    num = str(const)
    if "/" not in num:
        num += "/1"
    return "(poly.const " + num + ")"

def var_string(var):
    if "var" in var:
        var = var.replace("var", "")
        var = "(poly.var " + var + ")"
    return var

def mul_vars_string(var_list):
    if var_list == []:
        return const_string(1)
    elif len(var_list) == 1:
        return var_string(var_list[0])
    return "(poly.mul " + var_string(var_list[0]) + " " + mul_vars_string(var_list[1:]) + ")"

def monomial_to_string(m):
    m = str(m)
    m_list = m.replace(" ", "").split("*")
    var_things = m_list.copy()
    
    for var_thing in m_list:
        if "^" in var_thing:
            temp = var_thing.split("^")
            var_things.remove(var_thing)
            var_things += [temp[0]] * int(temp[1])
    return mul_vars_string(var_things)

def poly_terms_string(terms):
    if terms == []:
        return const_string(1)
    elif len(terms) == 1:
        return terms[0]
    return "(poly.sum " + terms[0] + " " + poly_terms_string(terms[1:]) + ")"

def polynomial_to_string(p):
    monomials = p.monomials()
    coeffs = p.coefficients()
    if len(monomials) == 0:
        return const_string(0)
    out = []
    for i in range(len(coeffs)):
        if str(monomials[i]) == "1":
            n = QQ(float(coeffs[i]))
            out.append(const_string(n))
        else:
            out.append("(poly.mul " + const_string(coeffs[i]) + " " + monomial_to_string(monomials[i]) + ")")
    return poly_terms_string(out)
'''

def type_str(type):
    # if type == "rat":
    #     return "QQ"
    # elif type == "int":
    #     return "ZZ"
    # elif type == "real":
    #     return "RR"
    # elif type == "complex":
    #     return "CC"
    return "QQ"

def var_names(var_list_string):
    out = ""
    var_list_string = var_list_string[1:-1]
    var_names = var_list_string.replace(" ", "")
    return var_names

def create_query(type: str, var_list, eq_list, goal_type):
    query = f'''
{var_names(var_list)} = {type_str(type)}['{var_names(var_list)}'].gens()
gens = {eq_list}
p = {goal_type}
basis, coeffs, r = ideal_membership(p, gens)
print(list(map(polynomial_to_string, coeffs[0])))
'''
    return query


def evaluate_in_sage(query: str, format=False) -> str:
    # clean_query = urllib.parse.quote(query)
    # It may be necessary to sanitize the query, but for now it seems to cause errors?
    if format:
        clean_query = query
        query = (f'print({clean_query})')
    data = {'code': query}
    headers = {'content-type': 'application/x-www-form-urlencoded'}
    response = requests.post('https://sagecell.sagemath.org/service', data, headers=headers)
    response = json.loads(response.text)
    if response['success']:
        return response['stdout'] if 'stdout' in response else None 
    else:
        raise Exception(response)

# print(evaluate_in_sage('5+8'))
# print(evaluate_in_sage('sin(3.1567)'))


def main():
    command = create_query(sys.argv[1], sys.argv[2], sys.argv[3], sys.argv[4])
    final_query = sage_functions + "\n" + command
    output = evaluate_in_sage(final_query).replace("'", "")
    output = output.replace(",", "")
    output = output.replace("[", "").replace("]", "").strip()
    output += " "
    print(output)

    # for elt in sys.argv[1:]:
    #     print(elt)

def alt():
    command = create_query("rat", "[var2, var1]",
     "[((var1 + var2) + (-1 * 0)), ((var1 * var1) + (-1 * 0))]", "(((2 * var1) + (2 * var2)) + (-1 * 0))")
    final_query = sage_functions + "\n" + command
    output = evaluate_in_sage(final_query).replace("'", "")
    output = output.replace(",", "")
    output = output.replace("[", "").replace("]", "").strip()
    output += " "
    print(output)

def alt2():
    command = create_query(sys.argv[1], sys.argv[2], sys.argv[3], sys.argv[4])
    print(command)
    # final_query = sage_functions + "\n" + command
    # output = evaluate_in_sage(final_query).replace("'", "")
    # output = output.replace(",", "")
    # output = output.replace("[", "").replace("]", "").strip()
    # output += " "
    # print(output)

if __name__ == "__main__":
    main()
    # alt()
    # alt2()