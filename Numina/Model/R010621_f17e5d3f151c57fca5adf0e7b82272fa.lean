import Mathlib

open scoped List

theorem number_theory_93411 (a b c d e : ℕ)
    (h : [a, b, c, d, e] ~ [71, 76, 80, 82, 91])
    (h2 : 2 ∣ d + e)
    (h3 : 3 ∣ c + d + e)
    (h4 : 4 ∣ b + c + d + e) : a = 80 := by
-- The sum of all scores is 400.
  -- The sum excluding the last score must be divisible by 4.
  have ha_dvd : 4 ∣ 400 - a := by
    have h_sum : 400 = a + b + c + d + e := by
      suffices 400 = List.sum [a, b, c, d, e] by simpa [← add_assoc] using this
      rw [h.sum_eq]
      norm_num
    convert h4 using 1
    refine Nat.sub_eq_of_eq_add' ?_
    simpa [← add_assoc]
  -- This only leaves two possibilities for the last score.
  have ha_two : a = 76 ∨ a = 80 := by
    have ha : a ∈ [71, 76, 80, 82, 91] := by simp [← h.mem_iff]
    simp only [List.mem_cons, List.mem_singleton, List.not_mem_nil, or_false] at ha
    cases ha with
    | inl ha => rw [ha] at ha_dvd; contradiction
    | inr ha =>
      cases ha with
      | inl ha => refine Or.inl ha
      | inr ha =>
        cases ha with
        | inl ha => refine Or.inr ha
        | inr ha =>
          cases ha with
          | inl ha => rw [ha] at ha_dvd; contradiction
          | inr ha => rw [ha] at ha_dvd; contradiction
  cases ha_two with
  | inl ha =>
    -- The sum excluding 76 is 324.
    -- The sum excluding the second-last score must be divisible by 3.
    have h : [b, c, d, e] ~ [71, 80, 82, 91] := by simpa [ha] using h.erase a
    have hb_dvd : 3 ∣ 324 - b := by
      have h_sum : 324 = b + c + d + e := by
        suffices 324 = List.sum [b, c, d, e] by simpa [← add_assoc] using this
        rw [h.sum_eq]
        norm_num
      convert h3 using 1
      refine Nat.sub_eq_of_eq_add' ?_
      simpa [← add_assoc]
    -- There are 4 possibilities for the second-last score.
    -- None of them leave a total that is divisible by 3.
    have hb : b ∈ [71, 80, 82, 91] := by simp [← h.mem_iff]
    simp only [List.mem_cons, List.mem_singleton, List.not_mem_nil, or_false] at hb
    cases hb with
    | inl hb => rw [hb] at hb_dvd; contradiction
    | inr hb =>
      cases hb with
      | inl hb => rw [hb] at hb_dvd; contradiction
      | inr hb =>
        cases hb with
        | inl hb => rw [hb] at hb_dvd; contradiction
        | inr hb => rw [hb] at hb_dvd; contradiction
  | inr ha => exact ha