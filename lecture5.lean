variables P Q R : Prop

theorem dm1: ¬ (P ∨ Q) ↔ ¬ P ∧ ¬ Q :=
begin
    constructor,
    assume npq,
    constructor,
    assume p,
    apply npq,
    left,
    exact p,
    assume q,
    apply npq,
    right,
    exact q,
    assume npnq pq,
    cases npnq with np nq,
    cases pq with p q,
    apply np,
    exact p,
    apply nq,
    exact q,
end

open classical

#check em P

theorem dm2 : ¬ (P ∧ Q) ↔ ¬ P ∨ ¬ Q :=
begin
  constructor,
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
  assume npnq pq,
  cases pq with p q,
  cases npnq with np nq,
  apply np,
  exact p,
  apply nq,
  exact q,
end

theorem raa : ¬ ¬ P → P :=
begin
  assume nnp,
  cases em P with p np,
  exact p,
  have f : false,
  apply nnp,
  exact np,
  cases f,
end

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