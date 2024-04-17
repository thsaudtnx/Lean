 variables P Q R : Prop
 variables A B C : Type
 variables PP QQ : A → Prop

 theorem curry_pred : (∃ x : A, PP x) → R ↔ (∀ x : A, PP x → R) :=
 begin
  constructor,
  assume ppr,
  assume a,
  assume pp,
  apply ppr,
  existsi a,
  exact pp,
  assume ppr,
  assume pp,
  cases pp with a p,
  apply ppr,
  exact p,
 end

 example : ∀ x : A, x=x :=
 begin
  assume a,
  reflexivity,
 end

example: ∀ x y : A, x=y → PP y → PP x :=
begin
  assume x y eq pp,
  rewrite eq,
  apply pp,
end

example : ∀ x y : A, x=y → PP x → PP y :=
begin
  assume x y eq pp,
  rewrite <- eq,
  exact pp,
end

example : ∀ x y : A, x=y → PP x → PP y :=
begin
  assume x y eq pp,
  rewrite eq at pp,
  exact pp,
end

theorem sym_eq : ∀ x y : A, x=y → y=x :=
begin
  assume x y eq,
  rewrite eq,
end

theorem trans_eq : ∀ x y z : A, x=y → y=z → x=z :=
begin
  assume x y z xy yz,
  rewrite xy,
  exact yz,
end

theorem trans_eq1 : ∀ x y z : A, x=y → y=z → x=z :=
begin
  assume x y z xy yz,
  rewrite <- xy at yz,
  exact yz,
end

theorem sym_eq1 : ∀ x y : A, x=y → y=x :=
begin
  assume x y eq,
  symmetry,
  exact eq,
end

theorem trans_eq2 : ∀ x y z : A, x=y → y=z → x=z :=
begin
  assume x y z xy yz,
  transitivity,
  exact xy,
  exact yz,
end

example : ∀ x y z : A, x=y → y=z → x=z :=
begin
  assume x y z xy yz,
  calc
    x = y : by exact xy
    ... = z : by exact yz,
end

theorem congr_arg : ∀ f : A → B, ∀ x y : A, x = y → f x = f y :=
begin
  assume f x y eq,
  rewrite eq,
end

theorem dm1_pred : ¬ (∃ x : A, PP x) ↔ ∀ x : A, ¬ PP x :=
begin
  constructor,
  assume pp a p,
  apply pp,
  existsi a,
  exact p,
  assume pp p,
  cases p with a ppa,
  apply pp,
  exact ppa,
end

constant raa : ¬ ¬ P → P 

theorem dm2_pred : ¬ (∀ x : A, PP x) ↔ ∃ x : A, ¬ PP x :=
begin
  constructor,
  assume npp,
  apply raa,
  assume ne,
  apply npp,
  assume a,
  apply raa,
  assume npp,
  apply ne,
  existsi a,
  exact npp,
  assume npp na,
  cases npp with a np,
  apply np,
  apply na,
end

variables B : Type
variables PPP : B → B → Prop
open classical

example : ∀ x y : B, PPP x y ∨ ¬ PPP x y :=
begin
  assume x y,
  cases em (PPP x y) with eq neq,
  left,
  exact eq,
  right,
  exact neq,
end









