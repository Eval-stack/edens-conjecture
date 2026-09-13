import EdensConjecture.EmbeddedStrangeProof.Attraction

noncomputable section
namespace Eden.StrangeProof.Direct

theorem hasDerivAt_negativeFlow {a t v : ℝ} (ha : 0 < a) (ht : 0 ≤ t) (hv : v ≤ 0) :
    HasDerivAt (fun s => negativeFlow a s v) ((negativeFlow a t v) ^ 2 - a ^ 2) t := by
  have hD := (negativeFlow_denominator_pos ha ht hv).ne'
  have he := ((hasDerivAt_id t).const_mul (-2 * a)).exp
  have hn := ((hasDerivAt_const t (a - v)).sub (he.const_mul (a + v))).const_mul (-a)
  have hd := (hasDerivAt_const t (a - v)).add (he.const_mul (a + v))
  have hg := hn.div hd hD
  convert! hg using 1 <;> simp only [negativeFlow, Pi.mul_apply, Pi.sub_apply, Pi.add_apply, id_eq]
  rw [div_pow, div_sub' (pow_ne_zero 2 hD)]
  congr 1
  ring

end Eden.StrangeProof.Direct
