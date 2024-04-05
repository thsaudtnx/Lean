open bool

def is_tt : bool → Prop
| ff := false
| tt := true

def implb : bool → bool → bool
| tt x := x
| ff x := true

def eqb: bool → bool → bool
| tt x := x
| ff x := ¬ x

-- BEGIN
theorem not_thm : ∀ x : bool, ¬ (is_tt x) ↔ is_tt (bnot x) :=
begin
  assume x,
  constructor,
  cases x,
  assume ntt,
  constructor,
  assume ntt,
  apply ntt,
  constructor,
  assume tt,
  cases x,
  assume ttff,
  cases ttff,
  cases tt,
end

theorem or_thm : ∀ x y : bool, is_tt x ∨ is_tt y ↔ is_tt (x || y) :=
begin
  assume x y,
  constructor,
  assume ttxtty,
  cases ttxtty with ttx tty,
  cases x,
  cases ttx,
  constructor,
  cases x,
  apply tty,
  constructor,
  assume ttxy,
  cases x,
  right,
  apply ttxy,
  left,
  constructor,
end
-- END