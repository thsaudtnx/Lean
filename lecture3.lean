variables P Q R : Prop

theorem swap : (P → Q → R) → (Q → P → R) :=
begin
  assume pqr q p,
  apply pqr,
  exact p,
  exact q,
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
  cases pq with q p,
  constructor,
  exact q,
  exact p,
end

theorem comAndIff : P ∧ Q ↔ Q ∧ P :=
begin
  constructor,
  apply comAnd,
  apply comAnd,
end

theorem comAndIff1 : P ∧ Q ↔ Q ∧ P :=
begin
  constructor,
  assume pq,
  cases pq with p q,
  constructor,
  exact q,
  exact p,
  assume qp,
  cases qp with q p,
  constructor,
  exact p,
  exact q,
end

theorem curry : P ∧ Q → R ↔ P → Q → R :=
begin
  constructor,
  assume pqr p q,
  apply pqr,
  constructor,
  exact p,
  exact q,
  assume pqr pq,
  cases pq with p q,
  apply pqr,
  exact p,
  exact q,
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