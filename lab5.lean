variables P Q R : Prop
variables A : Type
variables PP : A → Prop

theorem ex5q01 : (¬ P ∨ Q) → P → Q :=
begin
  assume npq p,
  cases npq with np q,
  have f : false,
  apply np,
  exact p,
  cases f,
  exact q,
end

open classical

theorem ex5q02 : ¬ (P ↔ ¬ P) :=
begin
  assume pnp,
  cases pnp with pnp npp,
  cases em P with p np,
  apply pnp,
  exact p,
  exact p,
  apply pnp,
  apply npp,
  exact np,
  apply npp,
  exact np,
end

theorem ex5q03 : ¬ P ↔ ¬ ¬ ¬ P :=
begin
  constructor,
  assume np nnp,
  apply nnp,
  exact np,
  assume nnnp p,
  apply nnnp,
  assume np,
  apply np,
  exact p,
end

theorem ex5q04 : ¬ ¬ (∀ x : A, PP x) → ∀ x : A, ¬ ¬ PP x :=
begin
  assume nnpp a npp,
  apply nnpp,
  assume pp,
  apply npp,
  apply pp,
end

constant raa : ¬ ¬ P → P

theorem ex5q05 : (∀ x : A, ¬ ¬ PP x) → ¬ ¬ ∀ x : A, PP x :=
begin
  assume nnpp npp,
  apply npp,
  assume a,
  apply raa,
  apply nnpp,
end