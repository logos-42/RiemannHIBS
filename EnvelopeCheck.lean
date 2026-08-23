import RiemannHIBS.Analytic

open RiemannHIBS.Analytic

-- 包络模块验证: expZeta / criticalLine_circle / zero_on_critical_line_envelope
#check expZeta
#check envelopeRadius
#check criticalLine_circle
#check zero_on_critical_line_envelope
#check criticalPhaseC_envelope_circle
#check zero_envelope_circle
#check expZeta_phase_principal
#check phase_periodic
#check phase_fold_neg_axis
#check phase_fold_many_sheets
#check envelope_universal_cover_branch
#check EnvelopeUniversalCoverMultiLog

-- 示例: 临界线 s = 1/2 + i·(π/4) 的包络点落在圆周 |w| = √e 上
example : ‖Complex.exp ((1 / 2 : ℂ) + Complex.I * ((Real.pi / 4 : ℝ) : ℂ))‖ = envelopeRadius :=
  criticalLine_circle (Real.pi / 4)
