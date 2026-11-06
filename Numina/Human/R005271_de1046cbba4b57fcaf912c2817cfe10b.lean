import Mathlib

open Finset

/-Soit $p \geqslant 3$ un nombre premier. Pour $k \in \mathbb{N}$ vérifiant $1 \leqslant k \leqslant p-1$, le nombre de diviseurs de $\mathrm{kp}+1$ qui sont compris strictement entre $k$ et $p$ est noté $a_{k}$.
Que vaut $a_{1}+a_{2}+\ldots+a_{p-1}$ ?-/
theorem number_theory_607290 (p : ℕ) (hp : p.Prime) (pge : 3 ≤ p) :
let D : ℕ → Finset ℕ := fun k => {d ∈ (k * p + 1).divisors| k < d ∧ d < p};
let a : ℕ → ℕ := fun k => (D k).card; ∑ i ∈ Ico 1 p, a i = p - 2 := by
-- Introduce assumptions and denote $B$ to be the set of sets of divisors in questions
  intro D a; let B := image D (Ico 1 p)
-- Prove that for any $k$ between $1$ and $p-1$, $D_k$ is a subset of $Ico 2 p$
  have Dsubs : ∀ s ∈ B, s ⊆ Ico 2 p := by
    intro s hs; simp [B] at hs; rcases hs with ⟨k, ⟨⟨kge, klt⟩, hk⟩⟩; rw [← hk]
    simp [D, Finset.subset_iff]; intros; constructor; all_goals linarith
-- Prove that any number $m$ between $2$ and $p-2$ occurs at most in one set of $B$
  have auxle : ∀ m ∈ Ico 2 p, (filter (fun (b : Finset ℕ) => m ∈ b) B).card ≤ 1 := by
    intro m; simp [card_le_one, Finset.ext_iff, B, D]; intro mge mlt
    intro A x xge xlt hA h B y yge ylt hB h' z
    rw [← hB, ← hA]; suffices : x = y; simp [this]
    obtain ⟨idvd1,xlt,_⟩ := (hA m).mpr h; obtain ⟨idvd2,ylt,_⟩ := (hB m).mpr h'
    suffices : (m : ℤ) ∣ x - y
    · by_contra! xney; replace this : m ≤ ((x : ℤ) - y).natAbs := by
        apply Int.natAbs_le_of_dvd_ne_zero at this; simp at this
        apply this; rw [sub_eq_zero]; norm_cast
      have := Int.natAbs_coe_sub_coe_lt_of_lt xlt ylt; linarith
    suffices : (m : ℤ) ∣ (x - y) * p
    · apply Int.dvd_of_dvd_mul_left_of_gcd_one this; norm_cast
      rw [Nat.gcd_comm]; apply Nat.coprime_of_lt_prime; any_goals linarith
      exact hp
    rw [show ((x:ℤ)-y)*p = x*p+1-(y*p+1) by ring]; apply dvd_sub; all_goals norm_cast
-- Prove that every number $m$ between $2$ and $p-2$ occurs at least in one set of $B$
  have auxge : ∀ m ∈ Ico 2 p, 1 ≤ (filter (fun (b : Finset ℕ) => m ∈ b) B).card := by
    intro m hm; simp [B, D]; simp at hm
    have copr : p.Coprime m := by apply Nat.coprime_of_lt_prime; linarith; linarith; exact hp
    obtain ⟨k, ⟨kge, klt, kdvd⟩⟩ : ∃ k, 1 ≤ k ∧ k < m ∧ m ∣ k * p + 1 := by
      rw [Nat.coprime_comm] at copr
      obtain ⟨k, hk⟩ := Nat.exists_mul_emod_eq_one_of_coprime copr (show _ by linarith)
      have kpos : 0 < k := by by_contra!; simp at this; simp [this] at hk
      use m * k / p % m; split_ands
      · by_contra! h; simp at h; rw [← Nat.dvd_iff_mod_eq_zero] at h
        have := Nat.mod_add_div (m*k) p; rw [hk] at this
        suffices : m ∣ 1; simp at this; linarith
        symm at this; rw [← Nat.sub_eq_iff_eq_add] at this; rw [← this]
        apply Nat.dvd_sub'; simp; rw [copr.dvd_mul_left]; exact h; linarith
      · apply Nat.mod_lt; linarith
      have := Nat.mod_add_div (m*k) p; rw [hk] at this; apply_fun fun t => t % m at this
      simp at this; rw [← Nat.dvd_iff_mod_eq_zero, ← Nat.mod_add_div (m*k/p) m] at this
      rw [Nat.mul_add, ← add_assoc, ← Nat.dvd_add_iff_left, add_comm, mul_comm] at this; exact this
      rw [← mul_assoc, mul_comm, ← mul_assoc]; simp
    use D k; simp [D]; split_ands
    · use k; split_ands; any_goals linarith
      rfl
    exact kdvd; all_goals linarith
-- Combine auxle and auxge, we get the following
  have aux : ∀ m ∈ Ico 2 p, (filter (fun (b : Finset ℕ) => m ∈ b) B).card = 1 := by
    intro m hm; specialize auxle m hm; specialize auxge m hm; linarith
-- Apply sum_card_inter on aux to get an equality on cardinalities, then rewrite it by sum_image' to get the final goal
  apply sum_card_inter at aux; simp [B] at aux; rw [← aux, sum_image']
-- Finish the rest trivial goals
  intro x hx; simp at hx; specialize Dsubs (D x) (show _ by simp [B]; use x)
  rw [← inter_eq_right] at Dsubs; rw [Dsubs]; by_cases emp : D x = ∅
  · simp [emp, a, sum_eq_zero]
  replace emp : (D x).Nonempty := by exact nonempty_iff_ne_empty.mpr emp
  obtain ⟨m, hm⟩ := emp; suffices : filter (fun j => D j = D x) (Ico 1 p) = {x}; simp [this]
  ext y; simp; constructor
  · rintro ⟨⟨yge, ylt⟩, hxy⟩; have hm' : m ∈ D y := by rw [hxy]; exact hm
    simp [D] at hm hm'; suffices : (m : ℤ) ∣ x - y
    · symm; by_contra! xney; replace this : m ≤ ((x : ℤ) - y).natAbs := by
        apply Int.natAbs_le_of_dvd_ne_zero at this; simp at this
        apply this; rw [sub_eq_zero]; norm_cast
      have := Int.natAbs_coe_sub_coe_lt_of_lt hm.right.left hm'.right.left; linarith
    suffices : (m : ℤ) ∣ (x - y) * p
    · apply Int.dvd_of_dvd_mul_left_of_gcd_one this; norm_cast
      rw [Nat.gcd_comm]; apply Nat.coprime_of_lt_prime; any_goals linarith
      exact hp
    rw [show ((x:ℤ)-y)*p = x*p+1-(y*p+1) by ring]; apply dvd_sub; all_goals norm_cast
    exact hm.left; exact hm'.left
  intro h; split_ands; any_goals linarith
  simp [h]