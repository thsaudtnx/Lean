variables P Q R: Prop

theorem I : P → P :=
begin
  assume p,
  exact p,
end

theorem C : (P → Q) → (Q → R) → P → R :=
begin
  assume pq qr p,
  apply qr,
  apply pq,
  exact p,
end

example : P → Q → P ∧ Q :=
begin
  assume p q,
  constructor,
  exact p,
  exact q,
end

theorem comAnd : P ∧ Q → Q ∧ P :=
begin
  assume pq,
  cases pq with p q,
  constructor,
  exact q,
  exact p,
end

example : P → P ∨ Q :=
begin
  assume p,
  left,
  exact p,
end

example : Q → P ∨ Q :=
begin
  assume q,
  right,
  exact q,
end

theorem case_lem : (P → R) → (Q → R) → P ∨ Q → R :=
begin
  assume pr qr pq,
  cases pq with p q,
  apply pr,
  exact p,
  apply qr,
  exact q,
end

example : true :=
begin
  constructor,
end

theorem efq : false → P :=
begin
  assume f,
  cases f,
end

theorem contr : ¬ (P ∧ ¬ P) :=
begin
  assume pnp,
  cases pnp with p np,
  apply np,
  exact p,
end

theorem q01 : (P → Q → R) → (P → Q) → P → R :=
begin
  assume pqr pq p,
  apply pqr,
  exact p,
  apply pq,
  exact p,
end

theorem q02 : P → (P → Q) → P ∧ Q :=
begin
  assume p pq,
  constructor,
  exact p,
  apply pq,
  exact p,
end

-- Q2. intuitionistic logic vs classical logic
-- intuitionistic logic : contructive proofs, rejects Law of Excluded Middle(LEM), negation x 
-- classical logic : non-constructive proofs, accepts Law of Excluded Middle(LEM), negation o

-- Q3. (a) Law of Excluded Middle(LEM)
--         P : P or not P , cases em P with p np
--     (b) LEM and RAA applied in the process of proving in Lean?

open classical

theorem dm2_em : ¬ (P ∧ Q) → ¬ P ∨ ¬ Q :=
begin
  assume npq,
  cases em P with p np,
  right,
  assume q,
  apply npq,
  constructor,
  exact p,
  exact q,
  left,
  exact np,
end

-- principle of Indirect Proof (RAA)
-- prove P is sufficient to show that not P is impossible
constant raa : ¬¬ P → P

theorem nn_em : ¬ ¬ (P ∨ ¬ P) :=
begin
  assume npnp,
  apply npnp,
  right,
  assume p,
  apply npnp,
  left,
  exact p,
end

theorem em : P ∨ ¬ P :=
begin
  apply raa,
  apply nn_em,
end

-- Q4. Construct a truth table for De Morgan's Law
-- P Q PorQ not(PorQ) notP notQ notPandnotQ iff


-- Q5. proposition vs predicate
-- proposition : true or false
-- predicate : proposition with variables

-- Q6. If all students are clever then if all clever students are funny then all students are funny.
variables A : Prop
variables PP QQ RR : A → Prop

example : (∀ x : A, PP x) → (∀ y : A, PP y → QQ y) → (∀ z : A, QQ z) :=
begin
  assume p pq a,
  apply pq,
  apply p,
end

-- Q7. Write Lean code to verify the reflexive, symmetric and transitive properties of an equivalence relation
theorem ref : ∀ x : A, x=x :=
begin
  assume x,
  refl,
end

theorem sym : ∀ x y : A, x=y → y=x :=
begin
  assume x y equal,
  rw equal,
end

theorem tran : ∀ x y z : A, x=y → y=z → x=z :=
begin
  assume x y z xy yz,
  rw xy,
end

-- Q8. Write the definition of bnot, band and bor for Boolean in Lean
def bnot : bool → bool
| ff := tt
| tt := ff

def band : bool → bool → bool
| ff b := ff
| tt b := b

def bor : bool → bool → bool
| ff b := b
| tt b := tt

-- Q9. (a) Define is_tt in Boolean
def is_tt : bool → Prop
| ff := false
| tt := true

-- Q9. (b) Write Lean code to show that tt and ff cannot be equal
example : tt ≠ ff :=
begin
  assume h,
  contradiction,
end

theorem cons : tt ≠ ff :=
begin
  assume h,
  change is_tt ff,
  rw <- h,
  trivial,
end

-- Q9. (c) Write Lean code to show that every element of bool is either tt or ff
example : ∀ x : bool, x=tt ∨ x=ff :=
begin
  assume x,
  cases x,
  right,
  refl,
  left,
  refl,
end

-- Q10. Observe the following definition. Work out the recursive steps for
def leb : N → N → bool
| zero n := tt
| (succ m) zero := ff
| (succ m) (succ n) := leb m n

def add : N → N → N
| m zero := m
| m (succ n) := succ (add m n)

-- (a) add 2 4 = add 2 (succ 3) = succ (add 2 3) = succ (add 2 (succ 2)) = succ (succ (add 2 2))
-- = succ (succ (add 2 (succ 1))) = succ(succ(succ(add 2 1))) = succ(succ(succ(add 2 (succ 0))))
-- = succ(succ(succ(succ(add 2 0)))) = succ(succ(succ(succ 2))) = succ(succ(succ 3)) = succ(succ 4)
-- = succ(succ 4) = succ 5 = 6

-- (b) leb 2 4 = leb (succ 1) (succ 3) = leb 1 3 = leb (succ 0) (succ 2) = leb 0 2 = tt

-- (c) leb 2 2 = leb (succ 1) (succ 1) = leb 1 1 = leb (succ 0) (succ 0) = leb 0 0 = tt

-- Q11. Explain briefly how insertion sort works
-- First, start with an unsorted list and you take a number from the front of the list each time and insert it at the appropriate position in ther already sorted list.
-- Inserting a number x, means going through the sorted list until a numer y, that is greater is found and then the number x is insert just before y.
-- There is also the special case that the sorted list is empty in which case the number will be just inserted directly into the front of the list

-- Q12. Write down the result of reduce(sort[6,3,8,2,3])
open nat
open list

def ble : N → N → bool
| 0 n := tt
| (succ m) 0 := ff
| (succ m) (succ n) := ble m n

def ins : N → list N → list N
| a [] := [a]
| a (b :: bs) := if ble a b then a :: b :: bs else b :: (ins a bs)

def sort : list N → list N
| [] := []
| (a :: as) := ins a (sort as)

#reduce (sort [6, 3, 8, 2, 3])

-- = sort (6 :: [3, 8, 2, 3]) 
-- = ins 6 (sort [3, 8, 2, 3]) 
-- = ins 6 (sort (3 :: [8, 2, 3])) 
-- = ins 6 (ins 3 (sort [8, 2, 3])) 
-- = ins 6 (ins 3 (sort (8 :: [2, 3]))) 
-- = ins 6 (ins 3 (ins 8 (sort [2, 3]))) 
-- = ins 6 (ins 3 (ins 8 (sort (2 :: [3])))) 
-- = ins 6 (ins 3 (ins 8 (ins 2 ( sort [3] )))) 
-- = ins 6 (ins 3 (ins 8 (ins 2 ( sort 3 :: [] )))) 
-- = ins 6 (ins 3 (ins 8 (ins 2 ( ins 3 (sort []))))) 
-- = ins 6 (ins 3 (ins 8 (ins 2 ( ins 3 []))))
-- = ins 6 (ins 3 (ins 8 (ins 2 (3 ::[]))))
-- = ins 6 (ins 3 (ins 8 (2 :: 3 ::[])))
-- = ins 6 (ins 3 (ins 8 (2 :: [3])))
-- = ins 6 (ins 3 (2 :: (ins 8 [3]))))
-- = ins 6 (ins 3 (2 :: [3, 8]))
-- = ins 6 (2 :: ins 3 [3, 8])
-- = ins 6 [2, 3, 3, 8]
-- = [2, 3, 3, 6, 8]

-- Q13. Write the Lean code definition of a binary tree with node labelled with natural numbers and explain it
inductive Tree : Type
| leaf : Tree
| node : Tree → N → Tree → Tree

-- leaf : represents a leaf node
-- node : left sub tree -> node value -> right sub tree