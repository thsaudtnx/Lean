variables P Q R: Prop

theorem I : P -> P :=
begin
  assume p,
  exact p,
end

theorem C : (P → Q) → (Q → R) → P → R :=
begin
  assume pq qr p,
  apply qr,
  apply pq,
  exact p,
end 
