import Mathlib

/- 62. In a $3 \times 3$ grid, fill in 9 different natural numbers such that the product of the three numbers in each row and the product of the three numbers in each column are all equal to P. Which of the 6 values 1996, 1997, 1998, 1999, 2000, 2001 can P take? -/
namespace number_theory_293628

def magic_square (a: Fin 3 → Fin 3 → Nat) (P: Nat) : Prop :=
    (∀ i, ∏j, a i j = P) ∧ (∀ j, ∏i, a i j = P)
    ∧ ∀ i j i' j', (i,j) ≠ (i',j') → a i j ≠ a i' j'

-- All numbers in the square need to be divisors of P
lemma lemma_1 (a : Fin 3 → Fin 3 → Nat) (P : Nat) (h: magic_square a P) : ∀ i j, a i j ∣ P := by
  intros i j
  obtain ⟨h, _ , _⟩ := h
  use a i (j+1) * a i (j+2)
  rw [← h i]
  rw [Fin.prod_univ_three]
  fin_cases j <;> simp <;> ring

-- P must have at least 9 distinct divisors, since there must be 9 distinct divisors of P in the square
lemma lemma_2 (a : Fin 3 → Fin 3 → Nat) (P : Nat) (h: magic_square a P) (h_pos: P≠0) : 9 ≤ P.divisors.card := by
  unfold magic_square at h
  have h_div := lemma_1 a P h
  obtain ⟨_, _, h_different⟩ := h
  let a_set : Finset ℕ := Finset.image (Function.uncurry a) Finset.univ
  have h_subset : a_set ⊆ P.divisors := by
    intro n h_mem
    unfold a_set at h_mem
    apply Finset.mem_image.mp at h_mem
    obtain ⟨⟨i,j⟩, _, h_n⟩ := h_mem
    subst n
    apply Nat.mem_divisors.mpr
    constructor
    case right => assumption
    case left => apply h_div
  have h_a_card : a_set.card = 9 := by
    unfold a_set
    rw [Finset.card_image_of_injective]
    simp
    case H =>
      unfold Function.Injective
      intro ij ij' h_eq
      by_contra h
      apply h_different ij.fst ij.snd ij'.fst ij'.snd
      · simp; assumption
      · unfold Function.uncurry at h_eq; assumption
  rw [← h_a_card]
  apply Finset.card_le_card
  apply h_subset

theorem number_theory_293628 (P : ℕ) :
    (∃ a, magic_square a P) ∧ P ∈ Finset.Icc 1996 2001 ↔ P = 1998 ∨ P = 2000 := by
  constructor
  case mp =>
    -- Of the numbers 1996 to 2001, only 1998 and 2000 have more than 8 divisors
    rintro ⟨⟨a, h_magic⟩, h⟩
    rw [Finset.mem_Icc] at h
    obtain ⟨h_lower, h_upper ⟩ := h
    have h := lemma_2 a P h_magic
    have h_pos : P ≠ 0 := by linarith
    specialize h h_pos
    interval_cases P
    case «1998» => trivial
    case «2000» => trivial
    all_goals exfalso
    case «1996» =>
      have : 9 > (Nat.divisors 1996).card := by native_decide
      linarith
    case «1997» =>
      have : 9 > (Nat.divisors 1997).card := by native_decide
      linarith
    case «1999» =>
      have : 9 > (Nat.divisors 1999).card := by native_decide
      linarith
    case «2001» =>
      have : 9 > (Nat.divisors 2001).card := by native_decide
      linarith
  case mpr =>
    -- for 1998 and 2000, we can construct a valid square
    intro h
    cases h
    case inl =>
      -- case 1998
      subst_vars
      constructor
      case right => simp
      case left =>
        use fun i j => match (i, j) with
        | (0,0) => 1
        | (0,1) => 6
        | (0,2) => 9*37
        | (1,0) => 27
        | (1,1) => 37
        | (1,2) => 2
        | (2,0) => 74
        | (2,1) => 9
        | (2,2) => 3
        unfold magic_square
        constructorm* _∧_
        case left =>
          intro i
          rw [Fin.prod_univ_three]
          fin_cases i
          all_goals simp
        case right.left =>
          intro j
          rw [Fin.prod_univ_three]
          fin_cases j
          all_goals simp
        case right.right =>
          intros i j i' j'
          fin_cases i<;> fin_cases j<;> fin_cases i'<;> fin_cases j' <;> simp
    case inr =>
      -- case 2000
      subst_vars
      constructor
      case right => simp
      case left =>
        use fun i j => match (i, j) with
        | (0,0) => 2
        | (0,1) => 5
        | (0,2) => 200
        | (1,0) => 40
        | (1,1) => 50
        | (1,2) => 1
        | (2,0) => 25
        | (2,1) => 8
        | (2,2) => 10
        unfold magic_square
        constructorm* _∧_
        case left =>
          intro i
          rw [Fin.prod_univ_three]
          fin_cases i
          all_goals simp
        case right.left =>
          intro j
          rw [Fin.prod_univ_three]
          fin_cases j
          all_goals simp
        case right.right =>
          intros i j i' j'
          fin_cases i<;> fin_cases j<;> fin_cases i'<;> fin_cases j' <;> simp
end number_theory_293628