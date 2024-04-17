open nat

def add : ℕ → ℕ → ℕ
| m  zero     := m
| m  (succ n) := succ (add m n)

def mul : ℕ → ℕ → ℕ
| m 0     := 0
| m (succ n) := (mul m n) + m

theorem add_rneutr : ∀ n : ℕ, n + 0 = n :=
begin
  assume n,
  refl,
end

theorem add_lneutr : ∀ n : ℕ, 0 + n = n :=
begin
  assume n,
  induction n with n' ih,
  refl,
  apply congr_arg succ,
  exact ih,
end

theorem add_assoc : ∀ l m n : ℕ , (l + m) + n = l + (m + n) :=
begin
  assume l m n,
  induction n with n' ih,
  refl,
  apply congr_arg succ,
  exact ih,
end

theorem mult_zero_r : ∀ n : ℕ , n * 0 = 0 :=
begin
  assume n,
  induction n with n' ih,
  refl,
  exact ih,
end