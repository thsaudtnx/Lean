variables P Q R : Prop

theorem ex4q01 : P → ¬ ¬ P :=
begin
  assume p np,
  apply np,
  exact p,
end

theorem ex4q02 : P ∧ true ↔ P :=
begin
  constructor,
  assume pt,
  cases pt with p t,
  exact p,
  assume p,
  constructor,
  exact p,
  constructor,
end

theorem ex4q03 : P ∨ false ↔ P :=
begin
  constructor,
  assume pf,
  cases pf with p f,
  exact p,
  cases f,
  assume p,
  left,
  exact p,
end

theorem ex4q04 : P ∧ false ↔ false :=
begin
  constructor,
  assume pf,
  cases pf with p f,
  exact f,
  assume f,
  constructor,
  cases f,
  exact f,
end

theorem ex4q05 : P ∨ true ↔ true :=
begin
  constructor,
  assume pt,
  cases pt with p t,
  constructor,
  exact t,
  assume t,
  right,
  exact t,
end

open classical

theorem ex4q06 : (P → Q) → ¬ P ∨ Q :=
begin
  assume pq,
  cases em P with p np,
  right,
  apply pq,
  exact p,
  left,
  exact np,
end

theorem ex4q07 : ((P → Q) → P) → P :=
begin
  assume pqp,
  cases em P with p np,
  exact p,
  apply pqp,
  assume p,
  have f : false,
  apply np,
  exact p,
  cases f,
end