import Mathlib

open Finset

/- Let $b \geq 2$ be a fixed integer, and let $s_{b}(n)$ denote the sum of the base- $b$ digits of $n$. Show that there are infinitely many positive integers that cannot be represented in the from $n+s_{b}(n)$ where $n$ is a positive integer. -/
theorem number_theory_604670 (b : ℕ) (hb : 2 ≤ b) : let s (n : ℕ) := (Nat.digits b n).sum;
((id + s) '' Set.univ)ᶜ.Infinite := by
-- Prove that $b-1$ divides $b^k-1$ for any number $k$
  have auxdvd : ∀ b > 1, ∀ k, (b - 1) ∣ b ^ k - 1 := by
    intro b hb k; rw [← Nat.modEq_iff_dvd']; calc
      _ ≡ 1 ^ k [MOD (b-1)] := by rw [one_pow]
      _ ≡ _ [MOD b-1] := by
        apply Nat.ModEq.pow; calc
          _ ≡ 0 + 1 [MOD b-1] := by rw [zero_add]
          _ ≡ (b - 1) + 1 [MOD b-1] := by apply Nat.ModEq.add; simp [Nat.ModEq]; rfl
          _ ≡ _ [MOD b-1] := by rw [Nat.sub_add_cancel]; linarith
    apply Nat.one_le_pow; linarith
-- Prove the following auxillary lemma by induction, it gives an alternative expression for numbers $rr...r$ in base $b$ with $r < b$
  have auxdig : ∀ b > 1, ∀ k, ∀ r < b, Nat.ofDigits b (List.replicate k r) = r * ((b ^ k - 1) / (b - 1)) := by
    intro b hb k; have : (b : ℚ) - 1 ≠ 0 := by
      intro h; rw [sub_eq_zero] at h; norm_cast at h; linarith
    induction k with
    | zero => simp
    | succ k ih =>
      intro r hr; rw [List.replicate_succ, Nat.ofDigits_cons, ih]; qify
      rw [Int.cast_div, Int.cast_div, Nat.cast_sub, Nat.cast_sub]; push_cast
      field_simp; ring; any_goals linarith
      apply Nat.one_le_pow; linarith
      any_goals norm_cast; apply auxdvd; linarith
      any_goals simp; intro h; rw [Nat.sub_eq_zero_iff_le] at h; linarith
-- To prove the main goal, we first rewrite it by Set.infinite_iff_exists_gt
  intro s; simp [Set.infinite_iff_exists_gt]; intro M
  have auxlt : M + 2 < b ^ (M + 2) := by apply Nat.lt_pow_self; omega
-- For any $x$ large enough, $x+s(x)$ is also large
  have ob1 : ∀ x, b ^ (2 * (M + 2)) ≤ x → b ^ (2 * (M + 2)) ≤ x + s x := by intro x xge; omega
-- Prove that if $x$ is between some large numbers, $x+s(x)$ is large
  have ob2 : ∀ x, b ^ (2 * (M + 2)) - M - 2 ≤ x → x ≤ b ^ (2 * (M + 2)) - 1 →
  b ^ (2 * (M + 2)) ≤ x + s x := by
    intro x xge xle; rw [Nat.sub_sub, Nat.sub_le_iff_le_add] at xge
  -- It suffices to show that the sum of the $b$-digits of $x$ is greater or equal to $M+1$
    suffices : M + 2 ≤ s x; omega; have : M + 2 ≤ (b - 1) * (M + 2) := by
      apply Nat.le_mul_of_pos_left; omega
  -- Rewrite $x$ and rearrange the terms
    apply le_trans this; replace this : x = b ^ (2 * (M + 2)) - b ^ (M + 2) +
    (b ^ (M + 2) - (b ^ (2 *(M + 2)) - x)) := by
      zify; repeat rw [Nat.cast_sub]
      push_cast; ring; any_goals omega
      apply Nat.pow_le_pow_right; all_goals omega
  -- Prove that the first $M+1$ $b$-digits of $x$ are $b-1$, therefore the inequality holds true
    rw [this]; simp only [s]; replace this : b ^ (2 * (M + 2)) - b ^ (M + 2) =
    b ^ (M + 2) * ((b - 1) * ((b ^ (M + 2) - 1) / (b - 1))) := by
      rw [Nat.mul_div_cancel' (by apply auxdvd; omega), Nat.mul_sub]; ring_nf
    rw [this]; replace this : (b.digits (b ^ (M + 2) - (b ^ (2 * (M + 2)) - x))).length ≤ M + 2 := by
      rw [Nat.digits_len]; simp; rw [← Nat.lt_add_one_iff, show M+1+1 = M+2 by ring]
      apply Nat.log_lt_of_lt_pow; suffices : 0 < b ^ (M + 2) - (b ^ (2 * (M + 2)) - x)
      any_goals omega
      apply Nat.sub_lt; positivity; rw [Nat.le_sub_iff_add_le] at xle; omega
      apply Nat.one_le_pow; omega
    nth_rw 2 [add_comm]; nth_rw 4 [← Nat.add_sub_cancel' this]
    rw [← Nat.digits_append_zeroes_append_digits, List.sum_append, List.sum_append]
    rw [List.sum_replicate, ← auxdig, Nat.digits_ofDigits, List.sum_replicate]
  -- Finish the rest trivial goals
    simp [mul_comm]; any_goals omega
    intro l hl; simp at hl; omega
    intro h; simp [List.getLast_replicate]; omega
    rw [Nat.mul_div_cancel' (by apply auxdvd; omega)]; omega
-- Preparing to use Nat.nth, we first define the following propositions $p$ for any number $n$
  let p : ℕ → Prop := fun n => (∀ (x : ℕ), ¬ x + s x = n) ∧ (n < b ^ (2 * (M + 2)))
-- Prove that $setOf p$ is finite
  have psubs : setOf p ⊆ range (b ^ (2 * (M + 2))) := by simp [Set.subset_def, p]
  have finp : (setOf p).Finite := by apply Set.Finite.subset _ psubs; apply finite_toSet
-- Prove the cardinality of $setOf p$ is larger than $M+1$
  have Mlt : M + 1 < finp.toFinset.card := by
    have : ((range (b ^ (2 * (M + 2)))) ∩
    (image (id + s) (Ico (b ^ (2 * (M + 2)) - M - 2) (b ^ (2 * (M + 2)))))) = ∅ := by
      rw [inter_comm]; simp [Finset.ext_iff]; intro a x xge xlt hax
      rw [← hax]; apply ob2; any_goals omega
    replace this : M + 2 ≤ ((range (b ^ (2 * (M + 2)))) \ (image (id + s) (range (b ^ (2 * (M + 2)))))).card := by
      rw [← sdiff_inter_self_left, card_sdiff]; simp
      have rangeU : range (b ^ (2 * (M + 2))) = (range (b ^ (2 * (M + 2)) - M - 2)) ∪
      (Ico (b ^ (2 * (M + 2)) - M - 2) (b ^ (2 * (M + 2)))) := by
        rw [range_eq_Ico, Ico_union_Ico_eq_Ico]; any_goals omega
      nth_rw 2 [rangeU]; rw [image_union, inter_union_distrib_left, this, union_empty]
      rw [Nat.le_sub_iff_add_le, ← Nat.le_sub_iff_add_le']; calc
        _ ≤ _ := card_le_card inter_subset_right
        _ ≤ _ := card_image_le
        _ = _ := by simp [Nat.sub_sub]
      apply le_of_lt; apply lt_trans auxlt; apply Nat.pow_lt_pow_right; any_goals omega
      calc _ ≤  _ := card_le_card inter_subset_left
        _ = _ := by simp
      exact inter_subset_left
    rw [Nat.lt_iff_add_one_le]; apply le_trans this; apply card_le_card
    simp [subset_iff, p]; intro a alt ha; constructor
    · intro x; by_cases hx : x < b ^ (2 * (M + 2)); exact ha x hx
      specialize ob1 x (by omega); omega
    exact alt
-- Fulfill the goal with $Nat.nth p (M+1)$ and prove it satisfies the desired properties
  use Nat.nth p (M + 1); have := Nat.nth_mem (M + 1) (by intro; exact Mlt)
  simp [p] at this; constructor; exact this.left; calc
    _ < M + 1 := by omega
    _ ≤ _ := by apply Nat.le_nth; intro; exact Mlt