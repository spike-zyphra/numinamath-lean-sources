import Mathlib

/- Bepaal alle paren $(a, b)$ van positieve gehele getallen waarvoor

$$
a^{2}+b \mid a^{2} b+a \quad \text { en } \quad b^{2}-a \mid a b^{2}+b .
$$ -/
theorem number_theory_605304 (a b : ℤ) (ha : 0 < a) (hb : 0 < b):
    a^2 + b ∣ a^2 * b + a ∧ b^2 - a ∣ a * b^2 + b ↔
    (a, b) = (a, a + 1) := by
    
    constructor

    --from left to right
    -- we first prove that a^2+b ∣ a-b^2 and a-b^2 ∣ a^2+b
    intro ⟨h1, h2⟩

    have lem1 : a^2 + b ∣ a-b^2 := by 
      have : a^2 + b ∣ a^2 + b := by exact Int.dvd_refl (a ^ 2 + b)
      have : a^2 + b ∣ b*(a^2+b) := by exact Int.dvd_mul_left b (a ^ 2 + b)
      have : a^2 + b ∣ (a^2*b+a) - b*(a^2+b) := by exact Int.dvd_sub h1 this
      have : a-b^2 = (a^2*b+a) - b*(a^2+b) := by ring_nf
      rw [this]; assumption
    have lem2 : b^2 - a ∣ a^2 + b := by 
      have : b^2 -a ∣ b^2 -a := by exact Int.dvd_refl (b ^ 2 - a)
      have : b^2 -a ∣a*(b^2-a) := by exact Int.dvd_mul_left a (b ^ 2 - a)
      have : b^2 -a ∣a*b^2 + b - (a*(b^2-a)) := by exact Int.dvd_sub h2 this
      have : a^2 + b = a*b^2 + b - (a*(b^2-a)) := by ring_nf
      rw [this]; assumption

    -- Then, we get a^2 + b = a-b^2 or a^2 + b = b^2 -a. And the first case is not possible.
    have : 0 ≤ a^2 + b := by nlinarith
    by_cases h: 0 ≤ a - b^2
    have lem2p : a - b^2 ∣ a^2 + b := by 
      have : -(b^2 - a) ∣ a^2 + b := by exact Int.neg_dvd.mpr lem2
      have : a - b^2 = -(b^2-a) := by ring_nf
      rw [this]; assumption
    have eq : a^2 + b = a - b^2 := by 
      apply Int.dvd_antisymm
      repeat assumption

    -- a^2 + b = b^2-a leads to that b = a + 1
    have : a^2 + b^2 = a - b := by omega
    have : a ≤ a^2 := by nlinarith
    have : -b < b^2 := by nlinarith
    linarith

    have : 0 ≤ b^2 -a := by linarith
    have lem1p: a^2 + b ∣ b^2 - a := by
      have : a^2 + b ∣ -(a-b^2) := by exact Int.dvd_neg.mpr lem1
      have : b^2 - a = -(a-b^2) := by ring_nf
      rw [this]; assumption
    have eq : a^2 + b = b^2 - a := by 
      apply Int.dvd_antisymm
      repeat assumption

    have eq2 : a^2 - b^2 = -(a+b) := by linarith
    have eq3 : (a+b)*(a-b) = -(a+b) := by linarith
    have eq4 : (a-b) = -1 := by nlinarith
    have : b = a + 1 := by linarith
    simp; assumption


    --from right to left. Simple calculation.
    intro hab; simp at hab
    rw [hab]; 
    constructor
    use a; ring_nf
    use (a+1); ring_nf
