

def test_coverage_curve_counts_tasks_not_samples():
    import pandas as pd
    from refactorproof.analyze import coverage_curve

    rows = []
    # task A: valid at attempt 2 only; task B: valid at attempts 0 and 3; task C: never
    for t, valids in [("A", {2}), ("B", {0, 3}), ("C", set())]:
        for k in range(5):
            rows.append({"model_id": "m", "task_id": t, "attempt": k, "original_proof_valid": k in valids})
    cc = coverage_curve(pd.DataFrame(rows), k_max=5).iloc[0]
    assert cc["tasks_attempted"] == 3
    assert abs(cc["coverage@1"] - 1 / 3) < 1e-9 and abs(cc["coverage@3"] - 2 / 3) < 1e-9 and abs(cc["coverage@5"] - 2 / 3) < 1e-9
