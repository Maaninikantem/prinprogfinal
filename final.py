from operator import truediv
from prolog_structures import Rule, RuleBody, Term, Function, Variable, Atom, Number
from typing import List
from functools import reduce

import sys
import random

class Not_unifiable(Exception):
	pass

'''
Please read prolog_structures.py for data structures
that represent Prolog terms, rules, and goals.
'''
class Interpreter:
	def __init__(self):
		pass

	'''
	Example
	occurs_check (v, t) where v is of type Variable, t is of type Term.
	occurs_check (v, t) returns true if the Prolog Variable v occurs in t.
	Please see the lecture note Control in Prolog to revisit the concept of
	occurs-check.
	'''
	def occurs_check (self, v : Variable, t : Term) -> bool:
		if isinstance(t, Variable):
			return v == t
		elif isinstance(t, Function):
			for t in t.terms:
				if self.occurs_check(v, t):
					return True
			return False
		return False


	'''
	Problem 1
	variables_of_term (t) where t is of type Term.
	variables_of_clause (c) where c is of type Rule.

	The function should return the Variables contained in a term or a rule
	using Python set.

	The result must be saved in a Python set. The type of each element (a Prolog Variable)
	in the set is Variable.
	'''
	def variables_of_term (self, t : Term) -> set :
		y = set()
		if isinstance(t, Variable):
			y.add(t)
		elif isinstance(t, Function):
			for i in t.terms:
					x = self.variables_of_term(i)
					y = y.union(x)
		return y
		

	def variables_of_clause (self, c : Rule) -> set :
		y = self.variables_of_term(c.head)
		z = self.variables_of_term(c.body)
		y = y.union(z)
		return y


	'''
	Problem 2
	substitute_in_term (s, t) where s is of type dictionary and t is of type Term
	substitute_in_clause (s, t) where s is of type dictionary and c is of type Rule,

	The value of type dict should be a Python dictionary whose keys are of type Variable
	and values are of type Term. It is a map from variables to terms.

	The function should return t_ obtained by applying substitution s to t.

	Please use Python dictionary to represent a subsititution map.
	'''
	
	def substitute_in_term (self, s : dict, t : Term) -> Term:
		x = set()
		if isinstance(t, Function):
			new_terms = []
			for term in t.terms:
				if term in s.keys():
						new_terms.append(s[term])
				else:
					new_terms.append(term)
			return Function(t.relation, new_terms)
		elif t in s.keys():
			x = s[t]
		else:
			x = t

		return x


	def substitute_in_clause (self, s : dict, c : Rule) -> Rule:
		if isinstance(c.head, Function):
			new_terms = []
			for term in c.head.terms:
				if term in s.keys():
					new_terms.append(s[term])
				else:
					new_terms.append(term)
			m1 = Function(c.head.relation, new_terms)
		
		if isinstance(c.body, Function):
			new_terms = []
			for term in c.body.terms:
				if term in s.keys():
					new_terms.append(s[term])
				else:
					new_terms.append(term)
			m2 = Function(c.body.relation, new_terms)

		return Rule(m1, c.body)
		

	'''
	Problem 3
	unify (t1, t2) where t1 is of type term and t2 is of type Term.
	The function should return a substitution map of type dict,s
	which is a unifier of the given terms. You may find the pseudocode
	of unify in the lecture note Control in Prolog useful.

	The function should raise the exception raise Not_unfifiable (),
	if the given terms are not unifiable.

	Please use Python dictionary to represent a subsititution map.
	'''
	
	def unify (self, t1: Term, t2: Term) -> dict:
		def ver_unify(t1, t2, acc_dict):
			x = self.substitute_in_term(acc_dict, t1)
			y = self.substitute_in_term(acc_dict, t2)
			if isinstance(x, Variable) and (not self.occurs_check(x, y)):
				for k in acc_dict.keys():
					acc_dict[k] = self.substitute_in_term({x : y}, acc_dict[k])
				acc_dict[x] = y
				return acc_dict
			elif isinstance(y, Variable) and (not self.occurs_check(y, x)):
				for k in acc_dict.keys():
					acc_dict[k] = self.substitute_in_term({y : x}, acc_dict[k])
				acc_dict[y] = x
				return acc_dict
			elif x == y:
				return acc_dict
			elif isinstance(x, Function) and isinstance(y, Function):
				for a, b in zip(x.terms, y.terms):
						result = ver_unify(a, b, acc_dict)
				return result
			else:
				raise Not_unifiable()

		final = ver_unify(t1, t2, {})
		return final
		
	
	
	fresh_counter = 0
	def fresh(self) -> Variable:
		self.fresh_counter += 1
		return Variable("_G" + str(self.fresh_counter))
	def freshen(self, c: Rule) -> Rule:
		c_vars = self.variables_of_clause(c)
		theta = {}
		for c_var in c_vars:
			theta[c_var] = self.fresh()

		return self.substitute_in_clause(theta, c)


	'''
	Problem 4
	Following the Abstract interpreter pseudocode in the lecture note Control in Prolog to implement
	a nondeterministic Prolog interpreter.

	nondet_query (program, goal) where
		the first argument is a program which is a list of Rules.
		the second argument is a goal which is a list of Terms.

	The function returns a list of Terms (results), which is an instance of the original goal and is
	a logical consequence of the program. See the tests cases (in src/main.py) as examples.
	'''
	def nondet_query (self, program : List[Rule], goal : List[Term]) -> List[Term]:
		while True:
			G = goal[:]
			res = goal[:]

			while res:
				p = self.freshen(program[random.randint(0, len(program)-1)])
				re = res[random.randint(0, len(res) -1)]
				try:
					self.unify(re, p.head)
				except:
					break
				res.remove(re)
				for term in p.body.terms:
					res.append(term)
				for term in res:
					res = [self.substitute_in_term(self.unify(re, p.head), term)]
				for term in G:
					G = [self.substitute_in_term(self.unify(re, p.head), term)]
			if not res:
				return G
			else:
				continue
	

	'''
	Challenge Problem

	det_query (program, goal) where
		the first argument is a program which is a list of Rules.
		the second argument is a goal which is a list of Terms.

	The function returns a list of term lists (results). Each of these results is
	an instance of the original goal and is a logical consequence of the program.
	If the given goal is not a logical consequence of the program, then the result
	is an empty list. See the test cases (in src/main.py) as examples.
	'''
	
	def det_query (self, program : List[Rule], pgoal : List[Term]) -> List[List[Term]]:
		g = pgoal[:]
		r = pgoal[:]
		def dfs(res, goal, solution):
			if not res:
				solution = solution.append(goal)
				return True
			while (res):
				chosen_goal = res.pop()
				searched = False
				for rule in program:
					if self.unify(rule.head, chosen_goal):
						Rule = self.freshen(rule)
						theta = self.unify(chosen_goal, rule.head)
						new_resolvent = res
						new_goal = goal
						for term in rule.body.terms:
							new_resolvent.append(term)
						new_resolvent = self.substitute_in_term(theta, new_resolvent)
						new_goal = self.substitute_in_term(theta, new_goal)
						result = dfs(new_resolvent, new_goal, solution)
						searched = searched or result
					if not searched:
						return []
		
		return dfs(self.unify, g, [])
	