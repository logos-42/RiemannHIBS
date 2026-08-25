---
title: RiemannHIBS 项目概览
source: session
created: 2026-08-25
tags: [overview]
schema_version: 2
audience: internal
last_confirmed: 2026-08-25
stage: current
---

# RiemannHIBS 项目概览

**一句话定义**: 用 HIBS 隐数运算法则（三公理 S/R/iR 标签流）构造黎曼 ζ/η 函数,
并把隐数标签连续化得到"包络结构"——临界线 Re s = 1/2 卷成圆周 |w| = √e 的
Lean 4 形式化 + 数值验证研究。

**主线目标**: 
1. 隐数三公理（A1 投影非单射 / A2 加减留 S 乘法投 R / A3 开方投 iR）承载 ζ/η 的级数结构
2. 解析延拓: η(s) = (1 − 2^{1−s})·ζ(s)（已证, 无 sorry）
3. 包络结构: 三标签 = 复平面锚定方向 {0, π/2, π}; 连续化 → 相位包络 ⟨r,θ⟩ ↦ r·e^{iθ};
   临界线像 = 圆 |w|=√e; 万有覆盖多圈叶
4. 诚实边界: RH 未证明; 所有"零点定理"是条件性/恒等式; 缺"圆外无零点"的核心机制

**交付**:
- Lean 4 (mathlib v4.28.0) 形式化, lake build 5858 jobs clean, 零 sorry
- 数值验证: experiments/envelope.py (E1 共圆 / E2 稠密 / E3 点列 / E4 绕数)
- 可视化: viz/fig1-10 + fig8 螺旋动画 GIF

**边界**: 值类型从 Int 到 ℝ/ℂ 的连续化已完成一半（EnvelopeC）; 多值 log 分支
(draft) 与 RH 本身是开放问题。
