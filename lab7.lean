open bool

local notation ! := bnot

theorem ex7q01 : ¬∀ x : bool, x ≠ x :=
begin
  assume neq,
  have f : tt ≠ tt,
  apply neq,
  apply f,
  refl,
end

theorem ex7q02 : ∀ x y : bool, x = y → ! x = ! y :=
begin
  assume x y eq,
  rw eq,
end

lemma ex7q03 : ∀ x : bool, x = !(!x) :=
begin
  assume x,
  cases x,
  refl,
  refl,
end

theorem dm1_b : ∀ x y : bool, bnot (x || y) = bnot x && bnot y :=
begin
  assume x y,
  cases x,
  refl,
  refl,
end

theorem dm2_b : ∀ x y : bool, bnot (x && y) = bnot x || bnot y :=
begin
  assume x y,
  cases x,
  refl,
  refl,
end