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
example : ∀ x y z : bool,
  x && (y || z) = x && y || x && z :=
begin
  assume x y z,
  cases z,
  sorry,
  sorry,
end
-- END
end bool

namespace bool

def is_tt : bool → Prop
| ff := false
| tt := true

--local notation x && y := band x y
--local notation x || y := bor x y

-- BEGIN
theorem and_thm : ∀ x y : bool, is_tt x ∧ is_tt y ↔ is_tt (x && y) :=
begin
  assume x y,
  constructor,
  assume h,
  cases h with xtt ytt,
  cases x,
  cases xtt,
  cases y,
  cases ytt,
  constructor,
  assume h,
  cases x,
  cases h,
  cases y,
  cases h,
  constructor,
  constructor,
  constructor,
end
-- END
end bool