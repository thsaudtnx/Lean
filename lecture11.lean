open list

namespace list

variables A B C: Type

inductive list (A : Type)
| nil : list
| cons : A → list → list

theorem no_conf : ∀ (a : A)(l : list A), nil ≠ a :: l :=
begin
  assume a l,
  contradiction,
end

def tl : list A → list A
| [] := []
| (a :: l) := l

theorem inj_tl : ∀ (a a': A)(l l' : list A), a :: l = a' :: l' → l = l' :=
begin
  assume a a' l l' h,
  change tl (a :: l) = tl (a' :: l'),
  rw h,
end

-- BEGIN
theorem inj_hd : ∀ (a a':A)(l l' : list A), a :: l = a' :: l' → a = a' :=
begin
  assume a a' l l' h,
  injection h,
end
-- END

def ins : N → list N → list N
| a [] := [a]
| a (b :: bs) := if ble a b then a :: b :: bs else b :: (ins a bs)

#reduce ins 6 [2, 3, 3, 8]

def sort : list N → list N
| [] := []
| (a :: as) := ins a (sort as)