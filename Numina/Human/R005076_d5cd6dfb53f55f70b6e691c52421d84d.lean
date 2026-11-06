import Mathlib

/- Vind alle viertallen $(a, b, c, d)$ van niet-negatieve gehele getallen zodat $a b=$ $2(1+c d)$ en er een niet-ontaarde driehoek bestaat met zijden van lengte $a-c, b-d$ en $c+d$. -/
theorem number_theory_605390 : {(a, b, c, d) : ℕ × ℕ × ℕ × ℕ | a * b = 2 * (1 + c * d) ∧
    ∃ x y z, x > 0 ∧ y > 0 ∧ z > 0 ∧ a - c = x ∧ b - d = y ∧ c + d = z ∧
    x + y > z ∧ y + z > x ∧ z + x > y} = {(1, 2, 0, 1), (2, 1, 1, 0)} := by
-- Rewrite the goal to a membership form and break `iff`
  simp [Set.ext_iff, and_assoc]; intro a b c d; constructor
  -- Introduce more variables and assumptions, then simplify the assumptions
  · rintro ⟨heq, ⟨x, xpos, y, ypos, z, zpos, hx, hy, hz, h1, h2, h3⟩⟩
    rw [← hx] at xpos h1 h2 h3; rw [← hy] at ypos h1 h2 h3
    rw [← hz] at zpos h1 h2 h3; clear x hx y hy z hz
    rw [show b-d+(c+d) = b+c by omega] at h2
    rw [show c+d+(a-c) = a+d by omega] at h3
    rw [Nat.sub_pos_iff_lt] at xpos ypos
    rw [← Nat.add_one_le_iff] at xpos ypos
    replace h1 : 2 * c + 2 * d < a + b := by omega
    replace h2 : a < b + 2 * c := by omega
    replace h3 : b < a + 2 * d := by omega
  -- Splite the goal to two cases
    rcases lt_or_le (2 * c) a with h|h
    -- When $2*c< a$, we can prove that $c<1$
    · have : 2 * c * d + 2 * c < a * b := by calc
        _ = 2 * c * (d + 1) := by ring
        _ ≤ 2 * c * b := by gcongr
        _ < _ := by gcongr; omega
      rw [heq, Nat.mul_add, mul_one, ← mul_assoc, add_comm] at this
      rw [add_lt_add_iff_right] at this
    -- Therefore $c=0$ and $a*b=2$, so $a=1$ and $b=2$
      replace this : c = 0 := by omega
      simp [this] at *; replace this : a ∣ 2 := by use b; rw [heq]
      rw [Nat.dvd_prime] at this; rcases this with h|h
      · simp [h] at heq; omega
      rw [h] at heq; omega; norm_num
  -- When $a≤ 2*c$, we can prove that $d<1$
    have : 2 * c * d + 2 * d < a * b := by calc
      _ = (c + 1) * (2 * d) := by ring
      _ < _ := by
        apply Nat.mul_lt_mul_of_le_of_lt xpos
        all_goals omega
    rw [heq, Nat.mul_add, mul_one, ← mul_assoc, add_comm] at this
    rw [add_lt_add_iff_right] at this
  -- Therefore $d=0$ and $a*b=2$, so $a=2$ and $b=1$
    replace this : d = 0 := by omega
    simp [this] at *; replace this : a ∣ 2 := by use b; rw [heq]
    rw [Nat.dvd_prime] at this; rcases this with h|h
    · simp [h] at heq; omega
    rw [h] at heq; omega; norm_num
-- Conversely, it is straightforward to check that when $a$, $b$, $c$ and $d$ are of the given values, all the required conditions hold true
  intro h; rcases h with ⟨ha, hb, hc, hd⟩|⟨ha, hb, hc, hd⟩
  all_goals norm_num [ha, hb, hc, hd]; repeat use 1; norm_num