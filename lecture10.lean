open nat

example : ∀ n : ℕ, 0 ≠ succ n :=
begin
  assume n h,
  contradiction,
end

namespace nat

def pre : ℕ → ℕ
 | zero := zero
 | (succ n) := n

#reduce (pre 7)

end nat

open nat

theorem inj_succ : ∀ m n : nat, succ m = succ n → m = n :=
begin
  assume m n h,
  change pred (succ m) = pred (succ n),
  rewrite h,
end

open nat

def double : ℕ → ℕ
| zero := 0
| (succ n) := succ (succ (double n))

#reduce (double 7)

open nat

def double : ℕ → ℕ
| zero := 0
| (succ n) := succ (succ (double n))

def half : ℕ → ℕ
| zero := zero
| (succ zero) := zero
| (succ (succ n)) := succ (half n)

#reduce (half 7)
#reduce (half (double 7))

open nat

-- BEGIN
theorem half_double : ∀ n : ℕ , half (double n) = n :=
begin
  assume n,
  induction n with n' ih,
  refl,
  dsimp [double,half],
  apply congr_arg succ,
  exact ih,
end
-- END

open nat
-- BEGIN

def add : ℕ → ℕ → ℕ
| m  zero     := m
| m  (succ n) := succ (add m n)

-- END

open nat

-- BEGIN
def mul : ℕ → ℕ → ℕ
| m 0     := 0
| m (succ n) := (mul m n) + m
-- END

open nat 

def eq_nat : ℕ → ℕ → bool
| zero     zero      := tt
| zero     (succ n)  := false
| (succ m) zero      := false
| (succ m) (succ n)  := eq_nat m n

open nat

 -- BEGIN
lemma eq_nat_ok_1 : ∀ n : ℕ , eq_nat n n = tt :=
begin
  assume n,
  induction n with n' ih,
  reflexivity,
  dsimp [eq_nat],
  exact ih,
end
-- END