import Mathlib

/-
PROBLEM:

In a parlor game, the magician asks one of the participants
to think of a three digit number (abc)(abc) where a, b, and c
represent digits in base 10 in the order indicated. The magician
then asks this person to form the numbers (acb), (bca), (bac),
(cab), and (cba), to add these five numbers, and to reveal their
sum, N. If told the value of N, the magician can identify the
original number, (abc)(abc). Play the role of the magician and
determine (abc) if N=3194.
-/

theorem number_theory_94882 (a b c: ℕ) (ha : a < 10) (hb : b < 10) (hc : c < 10)
(hN : 3194 = (100 * a + 10 * c + b) + (100 * b + 10 * a + c) +
(100 * b + 10 * c + a) + (100 * c + 10 * a + b) + (100 * c + 10 * b + a)) :
a = 3 ∧ b = 5 ∧ c = 8 := by {
  --simplify the equation
  ring_nf at hN
  let m := 100*a + 10*b + c
  --use the symmetry of the problem by adding (abc) to the other 5,
  --which reveals a congruence condition mod 222
  have hNpm : 3194 + m = 222*(a+b+c) := by {
    unfold m
    rw [hN]
    ring
  }
  have hmlt : m < 1000 := by linarith
  have : a + b + c ≥ 15 := by linarith
  have hmmod : ∃ k : ℕ, m = 222*k+136 := by {
    use (a+b+c)-15
    ring_nf
    rw [Nat.mul_sub_right_distrib]
    rw [mul_comm] at hNpm
    rw [←hNpm]
    unfold m
    simp
    calc a * 100 + b * 10 + c = 3330 + (a * 100 + b * 10 + c) - 3330 := by rw [Nat.sub_add_comm]; simp; linarith
                            _ = (136 + 3194) + (100 * a + 10 * b + c) - 3330 := by norm_num; rw [mul_comm,mul_comm b 10]
                            _ = 136 + (3194 + (100 * a + 10 * b + c) - 3330) := by rw [add_assoc,Nat.add_sub_assoc]; linarith
  }
  -- Since we are looking for a three digit number, this reduces to 4 cases,
  -- which we can just go through by hand.
  have hm : m = 358 := by {
    rcases hmmod with ⟨k,hk⟩
    have : k ≤ 3 := by linarith
    match k with
    | 0 => {
      simp at hk
      unfold m at hk
      have : a = 1 := by linarith
      rw [this] at hk
      simp at hk
      have : b = 3 := by linarith
      linarith
    }
    | 1 => trivial
    | 2 => {
      simp at hk
      unfold m at hk
      have : a = 5 := by linarith
      rw [this] at hk
      simp at hk
      have : b = 8 := by linarith
      linarith
    }
    | 3 => {
      simp at hk
      unfold m at hk
      have : a = 8 := by linarith
      rw [this] at hk
      simp at hk
      have : b = 0 := by linarith
      linarith
    }
  }
  have ha3 : (a = 3) := by linarith
  constructor
  linarith
  have hb5 : (b = 5) := by linarith
  constructor
  linarith
  linarith
}