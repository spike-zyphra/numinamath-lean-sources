import Mathlib

open Classical Finset

/-For how many pairs of nonzero integers $(c, d)$ with $-2015 \leq c, d \leq 2015$ do the equations $c x=d$ and $d x=c$ both have an integer solution?-/
theorem number_theory_609448 (hS : S = { P ∈ (Icc (-2015) 2015) ×ˢ (Icc (-2015) 2015) | P ≠ 0 ∧ (∃ x, P.1 * x = P.2) ∧ (∃ x, P.2 * x = P.1)}) :
S.card = 8060 := by
-- Generalize $2015$ to any positive integer $n$
  rw [show (2015:ℤ) = (2015:ℕ) by rfl] at hS
  have npos : 0 < 2015 := by simp
  rw [show 8060 = 4 * 2015 by simp]; generalize 2015 = n at npos hS
-- Define a fucntion $AV1$ to be the absolute value of the first coordinate
  let AV1 : ℤ × ℤ → ℕ := fun P => P.1.natAbs
-- Apply card_eq_sum_card_image to the function $AV1$ and $S$
  have Scard := card_eq_sum_card_image AV1 S
-- Prove the image set of $S$ under $AV1$ is $[1, n]$
  have Simg : image AV1 S = Icc 1 n := by
    ext x; simp [AV1, hS]; constructor
    · rintro ⟨c, ⟨⟨d, ⟨⟨cbd⟩, ⟨ne0, ⟨k1, hk1⟩, ⟨k2, hk2⟩⟩⟩⟩, hc⟩⟩
      replace hk1 : c ∣ d := by use k1; rw [hk1]
      replace hk2 : d ∣ c := by use k2; rw [hk2]
      rw [← Int.natAbs_dvd_natAbs] at hk1 hk2
      rw [← hc]; by_contra! h; by_cases h' : c.natAbs < 1
      · simp at h'; specialize ne0 h'; simp [h'] at hk1
        contradiction
      specialize h (by omega); omega
    intro hx; use x; constructor
    · use x; split_ands; any_goals omega
      use 1; simp; use 1; simp
    simp
-- Prove the filter set occured in the formula in Scard has card $4$
  have fcard : ∀ b ∈ image AV1 S, #(filter (fun a => AV1 a = b) S) = 4 := by
    simp [AV1, hS]; intro x c d cge cle dge dle ne0 k1 hk1 k2 hk2 hx
    have cne0 : c ≠ 0 := by
      by_contra!; specialize ne0 this
      simp [this] at hk1; symm at hk1; contradiction
    have card4 : ({(c, c), (c, -c), (-c, c), (-c, -c)} : Finset (ℤ × ℤ)).card = 4 := by
      simp [insert_eq]; repeat rw [card_union_of_disjoint]
      simp; simp; omega
      simp; constructor; intro; any_goals omega
      simp; omega
    rw [← card4]; congr; simp [Finset.ext_iff]; intro e f; constructor
    · rintro ⟨⟨efbd, ⟨ne0', ⟨⟨k1', hk1'⟩, ⟨k2', hk2'⟩⟩⟩⟩, he⟩
      replace hk1' : e ∣ f := by use k1'; rw [hk1']
      replace hk2' : f ∣ e := by use k2'; rw [hk2']
      rw [← Int.natAbs_dvd_natAbs] at hk1' hk2'
      have abseq : f.natAbs = e.natAbs := by
        rw [Nat.eq_iff_le_and_ge]; constructor
        · apply Nat.le_of_dvd; all_goals omega
        apply Nat.le_of_dvd; by_contra!; simp at this
        simp [this] at hk2'; all_goals omega
      rw [he] at abseq; rw [← hx, Int.natAbs_eq_natAbs_iff] at he abseq
      rcases he with he|he <;> rcases abseq with hf|hf
      all_goals rw [he, hf]; simp
    intro h; rcases h with ⟨he, hf⟩|⟨he, hf⟩|⟨he, hf⟩|⟨he, hf⟩
    all_goals split_ands; any_goals omega
    any_goals use 1; omega
    any_goals use -1; omega
-- Compute the card of $S$
  rw [Scard, sum_congr rfl fcard, Simg]; simp; ring