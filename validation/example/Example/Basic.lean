/-! Definitions used by `Example.Results`. -/

namespace Example

/-- Doubling. -/
def double (n : Nat) : Nat := n + n

theorem double_zero : double 0 = 0 := rfl

structure Point where
  x : Nat
  y : Nat

def Point.swap (p : Point) : Point := ⟨p.y, p.x⟩

notation "⦃" p "⦄" => Point.swap p

end Example
