variables P Q R : Prop

example : P ∧ (Q ∨ R) ↔ (P ∧ Q) ∨ (P ∧ R) :=
begin
  constructor,
  assume pqr,
  cases pqr with p qr,
  cases qr with q r,
  left,
  constructor,
  exact p,
  exact q,
  right,
  constructor,
  exact p,
  exact r,
  assume pqpr,
  cases pqpr with pq pr,
  cases pq with p q,
  constructor,
  exact p,
  left,
  exact q,
  cases pr with p r,
  constructor,
  exact p,
  right,
  exact r,
end

theorem case_thm : P ∨ Q → R ↔ (P → R) ∧ (Q → R) :=
begin
  constructor,
  assume pqr,
  constructor,
  assume p,
  apply pqr,
  left,
  exact p,
  assume q,
  apply pqr,
  right,
  exact q,
  assume prqr pq,
  cases prqr with pr qr,
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
  assume pigs_can_fly,
  cases pigs_can_fly,
end

theorem contr : ¬ (P ∧ ¬ P) :=
begin
  assume pnp,
  cases pnp with p np,
  apply np,
  exact p,
end

theorem I : P → P :=
begin
  assume p,
  exact p,
end



