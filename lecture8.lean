namespace bool

inductive bool : Type
| ff : bool
| tt : bool

namespace bool

def bnot : bool → bool
| tt := ff
| ff := tt

def band : bool → bool → bool
| tt b := b
| ff b := ff

def bor : bool → bool → bool
| tt b := tt
| ff b := b

example : ∀ x : bool, x=tt ∨ x=ff :=
begin
  assume x,
  cases x,
  right,
  refl,
  left,
  refl,
end

def is_tt : bool → Prop
| ff := false
| tt := true

theorem cons : tt ≠ ff :=
begin
  assume h,
  change is_tt ff,
  rewrite <- h,
  trivial,
end

example : tt ≠ ff :=
begin
  assume h,
  contradiction,
end


theorem distr_b : ∀ x y z : bool, x && (y || z) = z && y || x && z :=
begin
  assume x y z,
  cases x,
  dsimp [band, bor],
  refl,
  dsimp [band],
  refl,
end

namespace bool

def bnot : bool → bool
| tt := ff
| ff := tt

def band : bool → bool → bool
| tt b := b
| ff b := ff

def bor : bool → bool → bool
| tt b := tt
| ff b := b

-- BEGIN
theorem distr_b : ∀ x y z : bool,
  x && (y || z) = x && y || x && z :=
begin
  assume x y z,
  cases x,
  refl,
  refl,
end
-- END
end bool


