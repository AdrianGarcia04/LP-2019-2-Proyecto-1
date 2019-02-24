module Tableaux where

import Syntax

data Tableaux = Empty
             | Uno Prop Tableaux
             | Dos Tableaux Tableaux

-- Suponemos que las proposiones ya están en FNN
expand :: Tableaux -> Tableaux
expand tab = case tab of
    Empty -> Empty
    Uno phi t -> case phi of
        Conj p q -> expand (Uno p (Uno q t))
        Disy p q -> expand (Dos (Uno p t) (Uno q t))
        _ -> Uno phi (expand t)
    Dos t1 t2 -> Dos (expand t1) (expand t2)

trans :: Prop -> Tableaux
trans phi = expand (Uno phi Empty)

-- DFS
-- Dado un tableaux y una lista de variables
-- nos dice si el tableaux tiene un camino
-- que no contenga a ninguna de las negaciones
-- las variables en la lista dada
satisf_aux :: Tableaux -> [VarP] -> Bool
satisf_aux tab l = case tab of
    Empty -> True
    Uno phi t -> case phi of
        TTrue -> satisf_aux t l
        FFalse -> False
        V x -> if elem (-x) l
            then False
            else satisf_aux t (x:l)
        Neg (V x) -> if elem x l
            then False
            else satisf_aux t ((-x):l)
    Dos t1 t2 -> (satisf_aux t1 l) || (satisf_aux t2 l)

satisf_tab :: Prop -> Bool
satisf_tab phi = satisf_aux (trans (fnn phi)) []
