 variables P Q R : Prop
 variables A B C : Type
 variables PP QQ : A → Prop

example : (∀ x : A, PP x) → (∀ y : A, PP y → QQ y) → ∀ z : A , QQ z :=
begin
  assume pp qq,
  assume a,
  apply qq,
  apply pp,
end

example : (∀ x : A, PP x ∧ QQ x) ↔ (∀ x : A, PP x) ∧ (∀ x : A, QQ x) :=
begin
  constructor,
  assume ppqq,
  constructor,
  assume a,
  have ppqq : PP a ∧ QQ a,
  apply ppqq,
  cases ppqq with pp qq,
  exact pp,
  assume a,
  have ppqq : PP a ∧ QQ a,
  apply ppqq,
  cases ppqq with pp qq,
  exact qq,
  assume ppqq,
  cases ppqq with pp qq,
  assume a,
  constructor,
  apply pp,
  apply qq,
end

example : (∃ x : A, PP x) → (∀ y : A, PP y → QQ y) → ∃ z : A, QQ z :=
begin
  assume pp ppqq,
  cases  pp with a p,
  existsi a,
  apply ppqq,
  exact p,
end

example : (∃ x : A, PP x ∨ QQ x) ↔ (∃ x : A, PP x) ∨ (∃ x : A, QQ x) :=
begin
  constructor,
  assume ppqq,
  cases ppqq with a pq,
  cases pq with p q,
  left,
  existsi a,
  exact p,
  right,
  existsi a,
  exact q,
  assume ppqq,
  cases ppqq with pp qq,
  cases pp with a p,
  existsi a,
  left,
  exact p,
  cases qq with a q,
  existsi a,
  right,
  exact q,
end
