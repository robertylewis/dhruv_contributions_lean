import requests
import urllib.parse
import json
import sys

sage_functions = '''
from sage.structure.sequence import Sequence
import numpy as np

# some aliases that conform to Becker and Weispfenning's notation:
LCM = lambda f, g: f.parent().monomial_lcm(f, g)
LM = lambda f: f.lm()
LT = lambda f: f.lt()

def spol(f, g):
    fg_lcm = LCM(LM(f), LM(g))
    return fg_lcm//LT(f)*f - fg_lcm//LT(g)*g

def select(P):
    return min(P, key=lambda fi_fj: LCM(LM(fi_fj[0]),
                                        LM(fi_fj[1])).total_degree())

def one_hot(i,n):
    out = [0 for _ in range(n)]
    out[i] = 1
    return out

def my_buchberger(gens):
    n = len(gens)
    G = {gens[i] : one_hot(i, n) for i in range(n)}
    pairs = [(f,g) for f in gens for g in gens if f != g]
    
    while pairs:
        keys = set(G.keys())
        f,g = select(pairs)
        pairs.remove((f,g))
        
        h = spol(f,g).reduce(keys)
        if h != 0:
            pairs += [(h,j) for j in keys]
            fg_lcm = LCM(LM(f), LM(g))
            G[h] = [fg_lcm//LT(f) * G[f][i] - fg_lcm//LT(g) * G[g][i] for i in range(n)]
    return G

def grob_to_matrix(G, basis):
    A = []
    for g in basis:
        A.append(G[g])
    return A

def multi_div(f, gens):
    n = len(gens)
    quot = [0 for _ in range(n)]
    r = 0
    
    p = f
    while p != 0:
        i = 0
        division_occured = False
        
        while i < n and not division_occured:
            try:
                sub_q, sub_r = LT(p).quo_rem(LT(gens[i]))
            except:
                i += 1
            else:
                if sub_r == 0:
                    quot[i] += sub_q
                    p -= sub_q * gens[i]
                    division_occured = True
                else:
                    i += 1
        if division_occured == False:
            r += LT(p)
            p -= LT(p)
    return quot, r

def ideal_membership(p, gens):
    G = my_buchberger(gens)
    basis = list(G.keys())
    n = len(basis)
    
    quot, r = multi_div(p, basis)
    A = np.array(grob_to_matrix(G, basis))
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
        try:
            n = int(str(monomials[i]))
            out.append(const_string(n))
        except ValueError:
            out.append("(poly.mul " + const_string(coeffs[i]) + " " + monomial_to_string(monomials[i]) + ")")
    return poly_terms_string(out)
'''

def type_str(type):
    if type == "rat":
        return "QQ"
    elif type == "int":
        return "ZZ"
    elif type == "real":
        return "RR"
    elif type == "complex":
        return "CC"

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

if __name__ == "__main__":
    main()