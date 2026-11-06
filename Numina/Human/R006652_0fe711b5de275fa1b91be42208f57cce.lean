import Mathlib

/-!
# Existence of a Fibonacci multiple in Lean 4

We formalize the proof that for every positive integer `k`, there
exists `n > 0` such that `k ∣ fib n`.  We first show that the
`2×2` companion matrix over `ZMod k` powers to recover Fibonacci
numbers, then use the finiteness of `GL₂(ZMod k)`.
-/
open Nat


-- Every positive `k` divides some Fibonacci number.
theorem exists_fib_multiple {k : ℕ} (hk : 0 < k) : ∃ n, k ∣ fib n := by

  -- The Fibonacci companion matrix modulo `k`.
  let A := !![(0 : ZMod k), (1 : ZMod k); (1 : ZMod k), (1 : ZMod k)]
  let Matrix2x2 := Matrix (Fin 2) (Fin 2) (ZMod k)

  -- prove the `n`-th power of `A` recovers Fibonacci numbers.

  have fibMatrix_pow {k : ℕ} [NeZero k] : ∀ n ≥ 1,
  (!![(0 : ZMod k), (1 : ZMod k); (1 : ZMod k), (1 : ZMod k)]) ^ n =
    !![(fib (n - 1) : ZMod k), (fib n : ZMod k); (fib n : ZMod k), (fib (n + 1) : ZMod k)] := by

    let A := !![(0 : ZMod k), (1 : ZMod k); (1 : ZMod k), (1 : ZMod k)]

    intro n hn

    cases n with
    -- if n = 0, we can't prove the statement
    | zero =>
      linarith

    -- if n > 0, then the matrix is well-defined, so we can prove the statement
    | succ n' =>
      -- now `n = n' + 1`, so we do induction on `n' : ℕ`
      induction n' with
      | zero =>
        -- `fib (-1) = 0`, `fib 0 = 0`, `fib 1 = 1`, so identity matrix
        simp
      | succ m ih =>
        calc
          _ = A ^ (m + 2) := by congr
          _ = A ^ (m + 1) * A:= by
            simp only [pow_succ]

          -- use the induction hypothesis
          _ = !![↑(fib (m)), ↑(fib (m + 1)); ↑(fib (m + 1)), ↑(fib (m + 2))] * !![(0 : ZMod k), (1 : ZMod k); (1 : ZMod k), (1 : ZMod k)] := by
            congr
            have : m + 1 ≥ 1 := by
              simp [hn]
            simp only [A, ih this]
            norm_num

          _ = !![↑(fib (m + 1)), ↑(fib (m)) + ↑(fib (m + 1)); ↑(fib (m + 2)), ↑(fib (m + 1)) + ↑(fib (m + 2))] := by
            simp

          _ = !![↑(fib (m + 1)), ↑(fib (m + 2)); ↑(fib (m + 2)), ↑(fib (m + 3))] := by
            -- matrix multiplication implements F_{n+2} = F_{n+1} + F_n
            simp [Nat.fib_add_two]

  -- divide into cases: k = 1 and k ≥ 2
  by_cases h1 : k = 1
  · -- handle k = 1 directly
    use 1; simp [h1]

  . -- now k ≥ 2
    push_neg at h1
    have nz : k ≥ 2 := by omega
    haveI : NeZero k := ⟨by omega⟩

    -- view `fibMatrix` as an element of `GL₂(ZMod k)`

    have detA : (Matrix.det A : ZMod k) = -1 := by
      dsimp [A]
      simp [Matrix.det, Matrix.det_fin_two]

    have unit_detA : IsUnit (Matrix.det A) := by
      simp [detA]

    have unitA : IsUnit A := (Matrix.isUnit_iff_isUnit_det A).mpr unit_detA

    -- let `G:=GL₂(ZMod k)` be the general linear group over ZMod k
    let G := Matrix.GeneralLinearGroup (Fin 2) (ZMod k)

    let g := Matrix.GeneralLinearGroup.mk'' A unit_detA

    -- the general linear group is finite
    haveI : Fintype (Matrix.GeneralLinearGroup (Fin 2) (ZMod k)) := inferInstance

    let r := orderOf g

    have x : r ≤ Nat.card G:=by
      refine orderOf_le_of_pow_eq_one ?_ ?_
      exact card_pos
      exact pow_card_eq_one'

    -- the order of `g` is `r`
    have p_order : g ^ r = 1 := pow_orderOf_eq_one g

    -- the order of `g` is positive
    have : r > 0 := orderOf_pos g

    use r

    -- the (0, 1)-entry of `r`-th power of `A` recovers Fibonacci numbers `fib r`
    have h_eq: (!![(0 : ZMod k), (1 : ZMod k); (1 : ZMod k), (1 : ZMod k)]) ^ r = !![↑(fib (r - 1)), ↑(fib r); ↑(fib r), ↑(fib (r + 1))] := fibMatrix_pow (orderOf g) (by omega)

    -- the `r`-th power of `A` is the unit matrix, so `fib r` is divisible by `k`
    have h_mod: (fib r : ZMod k) = 0 := by
      calc
        _ = ((!![(0 : ZMod k), (1 : ZMod k); (1 : ZMod k), (1 : ZMod k)]) ^ r) 0 1 := by
          exact congrFun (congrFun (id (Eq.symm h_eq)) 0) 1
        _ = (g ^ r) 0 1 := by rfl
        _ = (1: G) 0 1 := by
          simp [p_order]
        _ = 0 := by
          simp

    exact (ZMod.natCast_zmod_eq_zero_iff_dvd (fib r) k).mp h_mod
