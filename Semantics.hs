module Semantics where

import Syntax
import Data.List

type Estado = [VarP]

interp :: Estado -> Prop -> Bool
interp e phi = case phi of
    TTrue -> True
    FFalse -> False
    V x -> elem x e
    Neg p -> not (interp e p)
    Conj p q -> (interp e p) || (interp e q)
    Disy p q -> (interp e p) && (interp e q)
    Imp p q -> not (interp e p) || (interp e q)
    Equiv p q -> (interp e p) == (interp e q)

estados :: Prop -> [Estado]
estados phi = subconj (vars phi)

-- 3. Conceptos semánticos

modelos :: Prop -> [Estado]
modelos phi = [e | e <- estados phi, interp e phi]

tautologia :: Prop -> Bool
tautologia phi = (modelos phi) == (estados phi)

satisfen :: Estado -> Prop -> Bool
satisfen = interp

satisf :: Prop -> Bool
satisf phi = modelos phi /= []

insatisfen :: Estado -> Prop -> Bool
insatisfen e phi = not (interp e phi)

contrad :: Prop -> Bool
contrad phi = modelos phi == []

pega :: [Prop] -> Prop
pega [] = TTrue
pega [x] = x
pega (x:xs) = Conj x (pega xs)

estadosConj :: [Prop] -> [Estado]
estadosConj l = estados (pega l)

modelosConj :: [Prop] -> [Estado]
modelosConj gamma = modelos (pega gamma)

satisfenConj :: Estado -> [Prop] -> Bool
satisfenConj e gamma = satisfen e (pega gamma)

satisfConj :: [Prop] -> Bool
satisfConj gamma = satisf (pega gamma)

insatisfenConj :: Estado -> [Prop] -> Bool
insatisfenConj e gamma = insatisfen e (pega gamma)

insatisfConj :: [Prop] -> Bool
insatisfConj gamma = contrad (pega gamma)

-- 4. Equivalencia de Fórmulas

equiv :: Prop -> Prop -> Bool
equiv p q = tautologia (Equiv p q)

-- 5. Consecuencia lógica

consecuencia :: [Prop] -> Prop -> Bool
consecuencia gamma phi = insatisfConj ((Neg phi):gamma)

argcorrecto :: [Prop] -> Prop -> Bool
argcorrecto gamma phi = consecuencia gamma phi

-- Auxiliares

vars :: Prop -> [VarP]
vars phi = case phi of
    TTrue -> []
    FFalse -> []
    V x -> [x]
    Neg p -> vars p
    Conj p q -> union (vars p) (vars q)
    Disy p q -> union (vars p) (vars q)
    Imp p q -> union (vars p) (vars q)
    Equiv p q -> union (vars p) (vars q)

subconj :: [a] -> [[a]]
subconj [] = [[]]
subconj (x:xs) = xs' ++ map (x:) xs'
    where xs' = subconj xs
