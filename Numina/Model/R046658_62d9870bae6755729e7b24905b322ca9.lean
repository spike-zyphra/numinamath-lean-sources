import Mathlib

theorem algebra_290612 :
  {x : ℝ | 
    let tamas_share := (x + 3) / 4
    let remain_after_tamas := (3 * x - 3) / 4
        
    let erzsi_share := (3 * x + 9) / 16
    let remain_after_erzsi := (9 * x - 21) / 16
        
    let bela_share := (9 * x + 27) / 64
    let remain_after_bela := (27 * x - 111) / 64
        
    let juliska_share := (27 * x + 81) / 256
    let remain_at_end := x - (tamas_share + erzsi_share + bela_share + juliska_share)
    tamas_share + bela_share = erzsi_share + juliska_share + (100 : ℝ )} =
  {1021} := by 
  ext x
  simp only [Set.mem_setOf_eq, Set.mem_singleton_iff]
  constructor
  · -- Assume the equation holds, prove x = 1021
    intro h
    have eq1 : (x + 3) / 4 + (9 * x + 27) / 64 = (3 * x + 9) / 16 + (27 * x + 81) / 256 + (100 : ℝ ) := by 
      linarith [h]
    linarith 
  · -- Assume x = 1021, prove the equation 
    intro h 
    rw [h]
    norm_num 
    all_goals norm_num 
    all_goals norm_num