
tm : Type
prop : Type
pred : Type


-- tm constructors
Z : tm
Succ : tm -> tm
Add : tm -> tm -> tm
Mult : tm -> tm -> tm

-- pred constructors, mutual with prop
Compr : (tm -> prop) -> pred

-- prop constructors, mutual with pred
Mem : tm -> pred -> prop
Forallt : (tm -> prop) -> prop
ForallP : (pred -> prop) -> prop
Imp : prop -> prop -> prop
