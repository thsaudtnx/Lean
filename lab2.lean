variables P Q R : Prop	

theorem ex2q01 : (P → Q) → (R → P) → (R → Q) := 
begin
  assume p2q r2p r,
  apply p2q,
  apply r2p,
  exact r,
end

theorem ex2q03 : (P → Q) → (Q → R) → (P → R) :=
begin
  assume p2q q2r p,
  apply q2r,
  apply p2q,
  exact p,
end

theorem ex2q04 : P → (P → Q) → P ∧ Q :=
begin
  assume p p2q,
  constructor,
  exact p,
  apply p2q,
  exact p,
end

theorem ex2q05 : (P → Q) → P ∧ R → Q ∧ R :=
begin
  assume p2q pr,
  cases pr with p r,
  constructor,
  apply p2q,
  exact p,
  exact r,
end

theorem ex2q06 : (P ∧ (Q ∧ R)) ↔ ((P ∧ Q) ∧ R) :=
begin
  constructor,
  assume pqr,
  cases pqr with p qr,
  cases qr with q r,
  constructor,
  constructor,
  exact p,
  exact q,
  exact r,
  assume pqr,
  cases pqr with pq r,
  cases pq with p q,
  constructor,
  exact p,
  constructor,
  exact q,
  exact r,
end

theorem ex2q07 : (P ∧ (Q ∧ R)) ↔ ((Q ∧ R) ∧ P) :=
begin
  constructor,
  assume pqr,
  cases pqr with p qr,
  cases qr with q r,
  constructor,
  constructor,
  exact q,
  exact r,
  exact p,
  assume qrp,
  cases qrp with qr p,
  cases qr with q r,
  constructor,
  exact p,
  constructor,
  exact q,
  exact r,
end