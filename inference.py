#!/usr/bin/env python

import re

class kb(object):
    def __init__(self, initialKb = []):
        self.facts = {
        'B' : ["(John,Alice)", "(John,Bob)"],
        'D' : ["(John,Alice)", "(John,Bob)"],
        'R' : ["(Tom)"],
        'Q' : ["(Bob)"],
        }
            
        self.clauses = {
        'H' : [('x', 'A(x)'), ('x', 'R(x)')],
        '~H' : [('y', 'D(x,y)')],
        'A' : [('x', 'B(x,y) ^ C(x,y)')],
        'C' : ['x,y', 'D(x,y) ^ Q(y)'],
        'G' : [('x','F(x)')],
        'H' : [('x','G(x)'), ('x', 'R(x)')],
        'F' : [('x','H(x)')],
        }
    
    def infer(self, quest):
        #hard coding the values here
        regex = re.compile('(\w+)\((.*)\)')
        m = re.match(regex, quest)
        
        print quest
        print m
        
        predicate = m.group(1)
        predArgs = m.group(2)
        constant = predArgs.split(",") #[x.strip for x in predArgs.split(",")]
        
        if predicate in self.facts:
            for fact in self.facts[predicate]:
                if predArgs == fact:
                    print "True"
                    return "True"
                
        if not predicate in self.clauses:
            print "False"
        
        for lhs in self.clauses[predicate]:        
            arguments =  lhs[0].split(',')
            unificatonRes = self.unify(arguments, constant)
            
            if unificatonRes:
                conjunctiveClauses = [x.strip() for x in lhs[1].split("^")]
                
                for clause in conjunctiveClauses:
                    unifiedClause = self.replaceWithTheta(clause, unificatonRes)
                    if not self.infer(unifiedClause):
                        break
                return True
            
            print unificatonRes
            
            print arguments
            print constant
        
        return False
    
    def replaceWithTheta(self, expr, thetaDict):
        print expr
        print thetaDict
        
        for variable, constant in thetaDict.iteritems():
            if variable in expr:    #this should be refined as it is very crude right now
                expr = expr.replace(variable, constant)
        
        return expr
    
    
    
    
    
    
    
    def isVariable(self, string):
        regex = re.compile("^[a-z]$")
        m = re.match(regex, string)
        
        if m:
            #print"true"
            return True
        else:
            #print "false"
            return False
    
    
    def unify(self, s1List, s2List):
        #need to standerdize here before unification
 
        unifierDict = {}        
        counter = 0
        
        for item in s1List:
            if (self.isVariable(item) and self.isVariable(s2List[counter])):
                print "both the items are varibale. need to look into this case"
                print "do nthing as this varibale cant be unified at this point"
            elif (not self.isVariable(item) and self.isVariable(s2List[counter])):
                unifierDict[s2List[counter]] = item
            elif (self.isVariable(item) and  not self.isVariable(s2List[counter])):
                unifierDict[item] = s2List[counter]
            else:
                print "false and cant be unified"
                return False
        print "True inside the unifier"
        return unifierDict
    
if __name__ == "__main__":
    kb_obj = kb()
    kb_obj.infer("F(Bob)")