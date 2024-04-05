variables P Q R : Prop

theorem ex3q01 : P ∨ Q → (P → Q) → Q :=
begin
  assume pq p2q,
  cases pq with p q,
  apply p2q,
  exact p,
  exact q,
end

theorem ex3q02 : P ∨ Q ↔ Q ∨ P :=
begin
  constructor,
  assume pq,
  cases pq with p q,
  right,
  exact p,
  left,
  exact q,
  assume qp,
  cases qp with q p,
  right,
  exact q,
  left,
  exact p,
end

theorem ex3q03 : P ∧ Q ↔ Q ∧ P :=
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

theorem ex3q04 : P ∧ (Q ∨ R) ↔ (P ∧ Q) ∨ (P ∧ R) :=
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

theorem ex3q05 : (P ∨ Q) ∨ R ↔ P ∨ (Q ∨ R) :=
begin
  constructor,
  assume pqr,
  cases pqr with pq r,
  cases pq with p q,
  left,
  exact p,
  right,
  left,
  exact q,
  right,
  right,
  exact r,
  assume pqr,
  cases pqr with p qr,
  left,
  left,
  exact p,
  cases qr with q r,
  left,
  right,
  exact q,
  right,
  exact r,
end

theorem ex3q06 : P ∨ (Q ∧ R) → (P ∨ Q) ∧ (P ∨ R) :=
begin
  assume pqr,
  cases pqr with p qr,
  constructor,
  left,
  exact p,
  left,
  exact p,
  cases qr with q r,
  constructor,
  right,
  exact q,
  right,
  exact r,
end

theorem ex3q07 : P ∨ Q → R ↔ (P → R) ∧ (Q → R) :=
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
  assume prqr,
  cases prqr with pr qr,
  assume pq,
  cases pq with p q,
  apply pr,
  exact p,
  apply qr,
  exact q,
end