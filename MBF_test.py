"""
Piotr Rzeźnik
"""

from MBF import MBF


with open("MBF_test") as test_file:
    print("Wyrażenie początkowe || Wyrażenie zredukowane || Wyrażenie oczekiwane || Czy redukcja jest poprawna? || Stopień redukcji")
    while line := test_file.readline().rstrip():
        expr, reduced, expected_reduction_level = line.split(":")
        expected_reduction_level = float(expected_reduction_level)
        f = MBF(expr)
        final_expr = f.minimize(False)
        if final_expr == "ERROR":
            reduction_level = -1.0
        else:
            reduction_level = round(len(final_expr)/len(f.expr), 2)
        print(expr + "  ||  " + final_expr + "  ||  " + reduced + "  ||  " + ("Tak" if expected_reduction_level == reduction_level else "Nie") + "  ||  " + str(reduction_level))


