import Mathlib
open Finset

-- Computes the total points from committees, with senators contributing $1$ point and aides contributing $1/4$ point per committee.
def committee_points (c : Finset (Finset ℕ)) (s : Finset ℕ) (a : Finset ℕ) : ℚ :=
  ∑ c_i ∈ c, ((filter (fun x => x ∈ s) c_i).card + (1/4 : ℚ) * (filter (fun x => x ∈ a) c_i).card)

/-In a certain country, there are 100 senators, each of whom has 4 aides. These senators and aides serve on various committees. A committee may consist either of 5 senators, of 4 senators and 4 aides, or of 2 senators and 12 aides. Every senator serves on 5 committees, and every aide serves on 3 committees. How many committees are there altogether?-/
theorem combinatorics_611107 (c : Finset (Finset ℕ)) (s : Finset ℕ) (a : Finset ℕ)
    (hs : s.card = 100) (ha : a.card = 400)
    (hsa : Disjoint s a)
    (hc : ∀ c_i ∈ c, c_i ⊆ s ∪ a ∧ (c_i.card = 5 ∧ c_i ⊆ s ∨
           c_i.card = 8 ∧ (filter (fun x => x ∈ s) c_i).card = 4 ∧ (filter (fun x => x ∈ a) c_i).card = 4 ∨
           c_i.card = 14 ∧ (filter (fun x => x ∈ s) c_i).card = 2 ∧ (filter (fun x => x ∈ a) c_i).card = 12))
    (hs_count : ∀ x ∈ s, (c.filter (fun c_i => x ∈ c_i)).card = 5)
    (ha_count : ∀ x ∈ a, (c.filter (fun c_i => x ∈ c_i)).card = 3)
    (h_points : committee_points c s a = 800) :
    c.card = 160 := by
  -- Computes the total service count of senators.
  have h_s_service : ∑ x ∈ s, (c.filter (fun c_i => x ∈ c_i)).card = 500 := by
    rw [sum_congr rfl (fun x hx => hs_count x hx)]
    rw [sum_const, hs]
    norm_num
  -- Computes the total service count of aides.
  have h_a_service : ∑ x ∈ a, (c.filter (fun c_i => x ∈ c_i)).card = 1200 := by
    rw [sum_congr rfl (fun x hx => ha_count x hx)]
    rw [sum_const, ha]
    norm_num
  -- Computes the total points.
  have h_total_points : ∑ c_i ∈ c, ((filter (fun x => x ∈ s) c_i).card + (1/4 : ℚ) * (filter (fun x => x ∈ a) c_i).card) = 800 := h_points
  -- Each committee contributes $5$ points.
  have h_committee_points : ∀ c_i ∈ c, (filter (fun x => x ∈ s) c_i).card + (1/4 : ℚ) * (filter (fun x => x ∈ a) c_i).card = 5 := by
    intro c_i hc_i
    rcases hc c_i hc_i with ⟨h_subset, h_type⟩
    rcases h_type with ⟨h_card_s, h_s⟩ | ⟨h_card, h_s_count, h_a_count⟩ | ⟨h_card, h_s_count, h_a_count⟩
    · have h_a_empty : filter (fun x => x ∈ a) c_i = ∅ := by
        ext x
        simp [mem_filter]
        intro h_x_c_i h_x_a
        have h_x_s : x ∈ s := h_s h_x_c_i
        absurd (mem_inter.mpr ⟨h_x_s, h_x_a⟩)
        rw [disjoint_iff_inter_eq_empty.mp hsa]
        exact not_mem_empty x
      have h_s_filter : filter (fun x => x ∈ s) c_i = c_i := by
        ext x
        simp [mem_filter]
        exact mem_of_subset h_s
      simp [h_a_empty, h_s_filter, h_card_s]
    · simp [h_s_count, h_a_count]; norm_num
    · simp [h_s_count, h_a_count]; norm_num
  -- Derive the mumber of committees.
  have h_c_card : c.card = 160 := by
    have h_sum : ∑ c_i ∈ c, (5 : ℚ) = 5 * c.card := by
      rw [sum_const, nsmul_eq_mul, mul_comm]
    rw [sum_congr rfl (fun c_i hc_i => h_committee_points c_i hc_i)] at h_total_points
    rw [h_sum] at h_total_points
    have h_div : c.card = (800 : ℚ) / 5 := by nlinarith
    norm_num at h_div
    exact_mod_cast h_div
  exact h_c_card
