module Semantics where
-- Modulo que define la semantica del proyecto
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

-- Obtiene una lista de estados de una proposicion
modelos :: Prop -> [Estado]
modelos phi = [e | e <- estados phi, interp e phi]

-- Dice si una proposicion es tautologia
tautologia :: Prop -> Bool
tautologia phi = (modelos phi) == (estados phi)

-- Dado un estado y una proposicion, determina si la proposicion es satisfacible bajo ese estado
satisfen :: Estado -> Prop -> Bool
satisfen = interp

-- Dice si una proposicion es satisfacible
satisf :: Prop -> Bool
satisf phi = modelos phi /= []

-- Dado un estado y una proposicion, determina si la proposicion es insatisfacible bajo ese estado
insatisfen :: Estado -> Prop -> Bool
insatisfen e phi = not (interp e phi)

-- Dice si una proposicion es una contradiccion
contrad :: Prop -> Bool
contrad phi = modelos phi == []

-- Metodo auxiliar que dada una lista de proposiciones, devuelve una sola
pega :: [Prop] -> Prop
pega [] = TTrue
pega [x] = x
pega (x:xs) = Conj x (pega xs)

-- Obtiene una lista de estados de una lista de proposiciones
estadosConj :: [Prop] -> [Estado]
estadosConj l = estados (pega l)

-- Obtiene una lista de modelos de una lista de proposiciones
modelosConj :: [Prop] -> [Estado]
modelosConj gamma = modelos (pega gamma)

-- Dado un estado y una lista de proposiciones, determina son satisfacibles bajo ese estado
satisfenConj :: Estado -> [Prop] -> Bool
satisfenConj e gamma = satisfen e (pega gamma)

-- Dice si una lista de proposiciones es satisfacible
satisfConj :: [Prop] -> Bool
satisfConj gamma = satisf (pega gamma)

-- Dado un estado y una lista de proposiciones, determina son insatisfacible bajo ese estado
insatisfenConj :: Estado -> [Prop] -> Bool
insatisfenConj e gamma = insatisfen e (pega gamma)

-- Determina si una lista de proposiciones es insatisfacible
insatisfConj :: [Prop] -> Bool
insatisfConj gamma = contrad (pega gamma)

-- 4. Equivalencia de Fórmulas

-- Dadas dos proposiciones, indica si son equivalentes
equiv :: Prop -> Prop -> Bool
equiv p q = tautologia (Equiv p q)

-- 5. Consecuencia lógica

-- Dada una lista de proposiciones y una consecuencia, determina si se cumple dicha consecuencia
consecuencia :: [Prop] -> Prop -> Bool
consecuencia gamma phi = insatisfConj ((Neg phi):gamma)

-- Dada una lista de proposiciones y una consecuencia, determina si el argumento es correcto
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
