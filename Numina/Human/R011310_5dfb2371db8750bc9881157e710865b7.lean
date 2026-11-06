import Mathlib

/-5. (FRG 1) ${ }^{\mathrm{IMO1}}$ The set $S=\{2,5,13\}$ has the property that for every $a, b \in S, a \neq b$, the number $a b-1$ is a perfect square. Show that for every positive integer $d$ not in $S$, the set $S \cup\{d\}$ does not have the above property.-/
theorem other_24042 : let S : Set ℤ := {2, 5, 13};
let P : Set ℤ → Prop := fun A => (∀ a ∈ A, ∀ b ∈ A, a ≠ b → IsSquare (a * b - 1));
(P S ∧ ∀ d, d ∉ S → ¬ P (S ∪ {d})) := by
-- Introduce assumptions and simplify them
  intro S P 
  apply And.intro
  · simp only [ne_eq, Set.mem_insert_iff, Set.mem_singleton_iff, forall_eq_or_imp, forall_eq,
    not_true_eq_false, Int.reduceMul, Int.reduceSub, Int.isSquare_ofNat_iff, IsEmpty.forall_iff,
    OfNat.ofNat_eq_ofNat, Nat.reduceEqDiff, not_false_eq_true, forall_const, true_and, and_true, P,
    S]
    native_decide
  intro d dniS PSud; simp only [P, S] at PSud dniS
  simp at dniS; push_neg at dniS; rcases dniS with ⟨dne2, dne5, dne13⟩
-- Obtain integers $x$, $y$ and $z$ by specializing the hypothesis PSud at $2$, $5$ and $13$ and unfolding the definition of IsSquare
  obtain ⟨x, hx⟩ := PSud 2 (show _ by simp) d (show _ by simp) (show _ by exact id (Ne.symm dne2))
  obtain ⟨y, hy⟩ := PSud 5 (show _ by simp) d (show _ by simp) (show _ by exact id (Ne.symm dne5))
  obtain ⟨z, hz⟩ := PSud 13 (show _ by simp) d (show _ by simp) (show _ by exact id (Ne.symm dne13))
-- Prove that $d$ must be odd
  have dodd : Odd d := by
    rw [← Int.not_even_iff_odd]; rintro ⟨k, hk⟩
    rw [hk, ← Int.ediv_add_emod x 4] at hx; ring_nf at hx
    have : 0 ≤ x % 4 := by apply Int.emod_nonneg; simp
    have : x % 4 < 4 := by apply Int.emod_lt; simp
    apply_fun fun t => t % 4 at hx
    rw [show x/4*(x%4)*8+(x/4)^2*16+(x%4)^2 = (x%4)^2+(x/4*(x%4)*2+(x/4)^2*4)*4 by ring] at hx
    repeat rw [Int.add_mul_emod_self] at hx
    simp at hx; interval_cases x % 4
    any_goals simp [pow_two] at hx
-- Prove that $y$ must be even and let $y$ equal $2y'$
  obtain ⟨y', hy'⟩ : Even y := by
    suffices : Even (y ^ 2)
    · rw [Int.even_pow] at this; simp at this; exact this
    rw [pow_two, ← hy]; rcases dodd with ⟨k, hk⟩
    use 5*k+2; rw [hk]; ring
-- Prove that $z$ must be even and let $z$ equal $2z'$
  obtain ⟨z', hz'⟩ : Even z := by
    suffices : Even (z ^ 2)
    · rw [Int.even_pow] at this; simp at this; exact this
    rw [pow_two, ← hz]; rcases dodd with ⟨k, hk⟩
    use 13*k+6; rw [hk]; ring
-- Subtract the hypothesis hz with hy and simplify
  apply_fun fun t => t - y * y at hz; nth_rw 1 [← hy] at hz
  rw [hy', hz'] at hz; ring_nf at hz
  rw [show d*8 = d*2*4 by ring, ← sub_mul, mul_left_inj', sq_sub_sq] at hz
-- If we can prove that $d$ is even from hz, we will get a contradiction since we have proved that $d$ is odd
  suffices : Even d
  · rw [← Int.not_odd_iff_even] at this; contradiction
-- Split the goal to two cases when $2$ divides $z'+y'$ or $z'-y'$ and prove in each case, $d$ has to be even
  obtain ⟨k, hk⟩|⟨k, hk⟩ : 2 ∣ z' + y' ∨ 2 ∣ z' - y' := by rw [← Prime.dvd_mul, ← hz]; simp; exact Int.prime_two
  · rw [show z'-y' = z'+y'-2*y' by ring, hk, mul_comm, mul_assoc, mul_right_inj'] at hz
    use k * (k - y'); rw [hz]; ring; simp
  rw [show z'+y' = z'-y'+2*y' by ring, hk] at hz; nth_rw 5 [mul_comm] at hz
  rw [← mul_assoc, mul_left_inj'] at hz; use (k + y') * k
  rw [hz]; ring; any_goals simp