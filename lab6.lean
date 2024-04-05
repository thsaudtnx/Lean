variables P Q R : Prop
variables A : Type
variables PP : A → Prop
variables RR : A → A → Prop
open classical

theorem ex6q01 : (∃ y : A, ∀ x : A, RR x y) → (∀ x:A, ∃ y : A , RR x y) :=
begin
  assume rr,
  assume a,
  cases rr with ee x,
  existsi ee,
  apply x,
end

theorem ex6q02 : ∀ x y : A, x = y → RR x y → RR x x :=
begin
  assume x y equal rr,
  rewrite equal at rr,
  rewrite equal,
  exact rr,
end

theorem ex6q03 : ∀ x y z : A, x = y → x ≠ z → y ≠ z :=
begin
  assume x y z xy xnotz ynotz,
  apply xnotz,
  rewrite xy,
  apply ynotz,
end

theorem ex6q04 : ∀ x y z : A, x ≠ y → (x ≠ z ∨ y ≠ z) :=
begin
  assume x y z nxy,
  cases em (y = z) with eq neq,
  left,
  assume xz,
  apply nxy,
  rewrite eq,
  exact xz,
  right,
  exact neq,
end

constant raa : ¬ ¬ P → P

theorem ex6q05 : ¬ (∀ x : A, PP x) → ∃ x : A, ¬ PP x :=
begin
  assume npp,
  apply raa,
  assume epp,
  apply npp,
  assume a,
  apply raa,
  assume npp,
  apply epp,
  existsi a,
  apply npp,
end