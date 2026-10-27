import Example.Basic

namespace Example

-- TODO: generalise to any semiring
theorem double_eq (n : Nat) : double n = 2 * n := by
  unfold double
  omega

theorem swap_swap (p : Point) : ⦃⦃p⦄⦄ = p := by
  cases p
  rfl

theorem double_double (n : Nat) : double (double n) = 4 * n := by
  rw [double_eq, double_eq]
  omega

def origin : Point := { x := 0, y := 0 }

instance : Inhabited Point := ⟨origin⟩

instance instReprPoint : Repr Point := ⟨fun p _ => repr (double p.x, p.y)⟩

end Example
