variables P Q R : Prop

theorem q01 : P → Q → P :=
begin
  assume p q,
  exact p,
end

theorem q02 : (P → Q → R) → (P → Q) → P → R :=
begin
  assume pqr pq p,
  apply pqr,
  exact p,
  apply pq,
  exact p,
end