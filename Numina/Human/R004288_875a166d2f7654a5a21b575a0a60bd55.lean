import Mathlib

open Real

/- 23. Given that $a, b, c$ are positive numbers satisfying $a^{2}=b^{2}+c^{2}$. Prove:

$$

a^{3}+b^{3}+c^{3} \geqslant \frac{2 \sqrt{2}+1}{7}\left[a^{2}(b+c)+b^{2}(c+a)+c^{2}(a+b)\right] .

$$
 -/
theorem inequalities_248985:
  IsLeast {D|∀ a b c :ℝ, 0 < a ∧ 0 < b ∧ 0 < c → (a+b)/(a+2*b) + (b+c)/(b+2*c) + (c+a)/(c+2*a) < D} ((5:ℝ)/2) := by
  unfold IsLeast lowerBounds; simp only [and_imp, Set.mem_setOf_eq]
  constructor
  · intro a b c ha hb hc
    -- we can write (a+b)/(a+2*b) = 1-(1/(a/b+2))
    have h0a: (a + b) / (a + 2 * b) = 1 - 1 / (a / b + 2) := by field_simp; ring_nf
    have h0b: (b + c) / (b + 2 * c) = 1 - 1 / (b / c + 2) := by field_simp; ring_nf
    have h0c: (c + a) / (c + 2 * a) = 1 - 1 / (c / a + 2) := by field_simp; ring_nf
    -- let x = a/b, y = b/c, z = c/a
    let q:∃ x:ℝ, x = a/b := by
      simp only [exists_eq]
    obtain ⟨x, xdef⟩ := q
    let q:∃ y:ℝ, y = b/c := by
      simp only [exists_eq]
    obtain ⟨y, ydef⟩ := q
    let q:∃ z:ℝ, z = c/a := by
      simp only [exists_eq]
    obtain ⟨z, zdef⟩ := q
    rw [h0a, h0b, h0c, ← xdef, ← ydef, ← zdef, show 1 - 1 / (x + 2) + (1 - 1 / (y + 2)) + (1 - 1 / (z + 2)) = 3 - (1 / (x + 2) + 1 / (y + 2) + 1 / (z + 2)) by ring_nf]
    suffices (1:ℝ)/2 < 1/(x+2) + 1/(y+2) + 1/(z+2) by linarith
    -- we can show that xyz=1
    have hxyz: x * y * z = 1 := by
      rw [xdef, ydef, zdef, show a / b * (b / c) * (c / a) = (a/a)*(b/b)*(c/c) by ring_nf, div_self (by positivity), div_self (by positivity),div_self (by positivity), mul_one, mul_one]
    -- get rid of the denominator
    apply (mul_lt_mul_right (a:=2*(x+2)*(y+2)*(z+2)) (by apply mul_pos; apply mul_pos; rw [xdef]; positivity; rw [ydef]; positivity; rw [zdef]; positivity)).mp
    rw [show 1 / 2 * (2 * (x + 2) * (y + 2) * (z + 2)) = (x + 2) * (y + 2) * (z + 2) by ring_nf,
        show (1 / (x + 2) + 1 / (y + 2) + 1 / (z + 2)) * (2 * (x + 2) * (y + 2) * (z + 2)) = 2 * ((x+2) / (x + 2)) * (y + 2) * (z + 2) + 2 * (x+2) * ((y + 2) / (y + 2)) * (z + 2) + 2 * (x+2) * (y + 2) * ((z + 2) / (z + 2)) by ring_nf,
        div_self (by rw [xdef]; positivity), div_self (by rw [ydef]; positivity), div_self (by rw [zdef]; positivity), mul_one, mul_one, mul_one
    ]
    -- simplify and finish
    suffices x * y * z < 16 + 4*(x+y+z) by linarith
    suffices 0 <x+y+z by linarith
    rw [xdef, ydef, zdef]; positivity
  · -- now we have to show that any number less than 5/2 can be exceeded
    intro D h
    by_contra hD; simp at hD

    suffices ∃ (a b c : ℝ), 0 < a ∧ 0 < b ∧ 0 < c ∧ (a + b) / (a + 2 * b) + (b + c) / (b + 2 * c) + (c + a) / (c + 2 * a) ≥ D by
      obtain ⟨a, b, c, ⟨ha, ⟨hb, ⟨hc, hl⟩⟩⟩⟩ := this
      specialize h a b c ha hb hc
      linarith
    clear h
    -- let's use x=t, y=t, z=1/t^2 with adequate t
    have he:∃e:ℝ, e > 0 ∧ D+e=5/2 := by
      exact exists_pos_add_of_lt' hD
    obtain ⟨e, hepos, heeq⟩ := he
    -- we use adequately large ratios to force the limit
    use 1, e^2, e^4
    constructor
    positivity
    constructor
    positivity
    constructor
    positivity
    rw [show D = 5/2-e by linarith]
    field_simp
    conv_rhs =>
      lhs; ring_nf
    conv_rhs =>
      rhs; ring_nf
    refine (div_le_div_iff₀ ?_ ?_).mpr ?_
    positivity
    positivity
    ring_nf
    suffices 0 ≤ e ^ 2 * 10 + e ^ 4 * 32 + e ^ 6 * 30 + e ^ 8 * 20 + e ^ 10 * 16 - (e ^ 2 * 10 - e ^ 3 * 4 + (e ^ 4 * 40 - e ^ 5 * 16) + (e ^ 6 * 45 - e ^ 7 * 18) + (e ^ 8 * 20 - e ^ 9 * 8) + (e ^ 10 * 20 - e ^ 11 * 8)) by linarith
    ring_nf
    -- complete the square
    rw [show e ^ 3 * 4 - e ^ 4 * 8 + (e ^ 5 * 16 - e ^ 6 * 15) + e ^ 7 * 18 + (e ^ 9 * 8 - e ^ 10 * 4) + e ^ 11 * 8 = e ^ 3 * (4 - e ^ 1 * 8 + (e ^ 2 * 16 - e ^ 3 * 15) + e ^ 4 * 18 + (e ^ 6 * 8 - e ^ 7 * 4) + e ^ 8 * 8) by ring_nf]
    apply mul_nonneg; positivity
    rw [show 4 - e ^ 1 * 8 + (e ^ 2 * 16 - e ^ 3 * 15) + e ^ 4 * 18 + (e ^ 6 * 8 - e ^ 7 * 4) + e ^ 8 * 8 = (2-2*e)^2 + e ^ 2 * ((3-4*e)^2+3+9*e + 2*e^2 + e ^ 4 * ((2-2*e)^2 + 4 + e * 4 + e ^ 2 * 4)) by ring_nf]
    positivity