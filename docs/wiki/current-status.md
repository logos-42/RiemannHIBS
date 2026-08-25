---
title: RiemannHIBS 当前状态
source: session
created: 2026-08-25
tags: [status]
schema_version: 2
audience: internal
last_confirmed: 2026-08-25
stage: current
---

# 当前状态 (2026-08-25)

## 已证 (无 sorry)
| 定理 | 位置 | 内容 |
|------|------|------|
| criticalLine_circle | Analytic.lean §6 | ‖exp(1/2+it)‖ = √e: 临界线像 = 圆周 |
| eta_eq_mul_zeta | Analytic.lean §4 | η = (1−2^{1−s})·ζ (Re s>1) |
| criticalPhaseC_envelope_circle | §7 | 相位截面经指数映射共圆 √e |
| expZeta_phase_principal | §8 | ζ̂(r·e^{iθ}) = ζ(log r + iθ) 主支 |
| phase_periodic / fold | §8 | 多圈叶 2πk 周期; 叶 π+2πk 折叠到负实轴 |
| envelope_universal_cover_branch | §8 | 每圈 k 有主支相位原像 |

## 声明 (非证明)
- RiemannHypothesisHidden / C / Phase: RH 的隐数翻译
- riemannHypothesis_hidden_of_mathlib: 经典 RH ⟹ 隐数版 (单向)
- EnvelopeUniversalCoverMultiLog: 多值 log 分支 (draft)

## 诚实边界 (核心!)
- 机制链最后一步"圆外无零点" = RH 本身, 被当前提, 未证明
- zero_envelope_circle 的 hζ 参数未使用 → "零点定理"实为纯几何恒等式
- 螺旋无限延伸 ≠ 全称证明: 舞台(覆盖)完备 ≠ 演员(零点)在台上

## 候选机制 (等价/直觉, 非力迫)
- 欧拉乘积正性 → Re s ≥ 1 无零点 (已证)
- Bohr–Landau/Selberg → 几乎所有零点在临界线附近 (密度)
- Möbius 平方根界: RH ⟺ M(x) = O(x^{1/2+ε}) (等价)
- Berry–Keating xp 量子化 (speculative)
- 频率干涉: Z(t) ≈ 2Σ n^{-1/2}cos(θ−t·log n) (Riemann–Siegel, 数值验证)

## 图
全部 fig1–fig10 已登记于 `manifests/raw_sources.csv` (status=new)。

- fig1 `viz/fig1_projection_cross.png` 投影十字 (S/R/iR 三标签 → 复平面)
- fig2 `viz/fig2_envelope_shell.png` 三维包络壳
- fig3 `viz/fig3_critical_section.png` 临界截面
- fig4 `viz/fig4_phase_cover.png` 相位覆盖
- fig5 `viz/fig5_covering_space.png` + `viz/fig5_rollup.png` 覆盖空间 / 卷绕成圆周 |w|=√e (零点编号对应)
- fig6 `viz/fig6_winding.png` 绕数 (argument principle: 像曲线绕原点圈数 = 零点数)
- fig7 `viz/fig7_three_views.png` 三视图
- fig8 `viz/fig8_spiral_animation.gif` 螺旋动画 (万有覆盖螺旋柱面)
- fig9 `viz/fig9_mobius_walk.png` Möbius 行走
- fig10 `viz/fig10_zero_vibration.png` 频率干涉 Z(t)≈2Σn^{-1/2}cos(θ−t·log n) (Riemann–Siegel 数值)

数值验证图 (experiments/):
- `experiments/envelope_critical.png` 临界线圆周 |w|=√e 与零点共圆验证 (E1)
- `experiments/envelope_plane.png` 复平面/包络平面视图
- `experiments/envelope_surface.png` 包络曲面 w=log z (螺旋柱面/万有覆盖)
