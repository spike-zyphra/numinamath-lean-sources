import Mathlib

namespace number_theory_302986

-- These are checked much faster and don't lead to "max heartbeats" when put outside.

def s := ((Finset.Icc 0 31
  ).image fun a => ((a, (1009 - a ^ 2).sqrt) : ℕ × ℕ)
  ).filter fun (a, b) => b ^ 2 = 1009 - a ^ 2

def t := ((((((s.biUnion fun (m, n) => {((22 + m : ℤ), n), ((22 - m : ℤ), n)}
  ).filter fun (a, _) => a ≥ 0
  ).image fun (a, n) => (a.toNat, n)
  ).biUnion fun (a, n) => {(a, (22 + n : ℤ)), (a, (22 - n : ℤ))})
  ).filter fun (_, b) => b ≥ 0
  ).image fun (a, b) => (a, b.toNat)

lemma t_eq : t = {(37, 50), (7, 50), (50, 37), (50, 7)} := by
  native_decide

theorem number_theory_302986 :
    { (a, b) : ℕ × ℕ |
      0 < a + b ∧ ((a ^ 2 + b ^ 2) / (a + b))^2 + ((a ^ 2 + b ^ 2) % (a + b)) = 1977 }
    = {(50,37),(50,7),(37,50),(7,50)} := by
  ext ⟨a, b⟩
  constructor
  · -- Forward direction: prove every pair meeting this criterion is in the set.
    intro hab
    rcases hab with ⟨a_add_b_pos, eq_1977⟩
    -- Given $a^{2}+b^{2}=q(a+b)+r$, $ q^{2}+r=1977 $
    have h_div_add_mod := Nat.div_add_mod (a ^ 2 + b ^ 2) (a + b)
    have h_mod_lt := Nat.mod_lt (a ^ 2 + b ^ 2) a_add_b_pos
    set q := (a ^ 2 + b ^ 2) / (a + b)
    set r := (a ^ 2 + b ^ 2) % (a + b)
    -- If $q \geq 45$, then $q^2 \geq 2025 > 1977$, a contradiction.
    have q_lt_45 : q < 45 := by nlinarith
    -- If $q \leq 43$, then $a + b > r \ge 1977 - 43^ 2 = 128$, also a contradiction.
    have q_gt_43 : q > 43 := by
      by_contra
      have : a + b > 128 := by
        nlinarith
      have : q ≥ 63 := by
        have : a ^ 2 + b ^ 2 ≤ (q + 1) * (a + b) := by
          linarith
        have : (a + b) ^ 2 ≤ 2 * (a ^ 2 + b ^ 2) := by
          exact add_sq_le
        nlinarith
      linarith
    -- Hence $q=44$, $r=41$, and $a^{2}+b^{2}=44(a+b)+41$.
    -- q is therefore 44
    interval_cases q
    have r_eq : r = 41 := by omega
    clear q_gt_43 q_lt_45
    --This simplifies to $(a-22)^{2}+(b-22)^{2}=1009$. The solutions are $(a, b)=(50,37),(50,7),(37,50),(7,50)$.
    rw [r_eq] at h_div_add_mod
    zify at h_div_add_mod
    have : ((a - 22) ^ 2 + (b - 22) ^ 2 : ℤ) = 1009 := by
      linarith
    let m := (a - 22 : ℤ).natAbs
    let n := (b - 22 : ℤ).natAbs
    have : m ^ 2 + n ^ 2 = 1009 := by
      zify
      repeat rw [Int.natAbs_sq]
      linarith
    have : m ≤ 31 := by nlinarith
    have : (m, n) ∈ s := by
      simp [s]
      constructor
      . use m, this
        simp
        rw [show 1009 - m ^ 2 = n ^ 2 by omega]
        exact Nat.sqrt_eq' n
      . omega
    have a_b_in : (a, b) ∈ t := by
      simp [t]
      use a, b
      constructor
      . constructor
        . use a, n
          constructor
          . use a
            constructor
            . constructor
              . use m, n
                simp [this]
                omega
              . simp
            . simp
          . simp
            omega
        . simp
      . simp
    rw [t_eq] at a_b_in
    set set := ({(50, 37), (50, 7), (37, 50), (7, 50)} : Set (ℕ × ℕ))
    let finset := ({(50, 37), (50, 7), (37, 50), (7, 50)} : Finset (ℕ × ℕ))
    have : set = finset := by
      simp [finset, set]
    rw [this]
    simp
    convert a_b_in using 1
    . unfold finset
      decide
    --exact a_b_in
  · -- Backward direction: prove that for each pair in the set, these conditions hold.
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff, Nat.reduceLeDiff, List.append_assoc,
      List.singleton_append, Set.mem_setOf_eq]
    rintro (h | h | h | h) <;>
    · cases h
      simp

end number_theory_302986
