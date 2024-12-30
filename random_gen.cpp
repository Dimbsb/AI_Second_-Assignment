#include <iostream>
#include <vector>
#include <unordered_set>
#include <algorithm>
#include <cstdlib>
#include <ctime>
#include <sstream>

using namespace std;

// Global variables for parameters
int numProblems, numVariables, numClauses, maxTries, maxFlips;
double negativeProbability, a;

// Δημιουργία τυχαίου literal με βάση την πιθανότητα εμφάνισης αρνητικού literal
int generateLiteral() {
    int literal = rand() % numVariables + 1; // Από 1 έως numVariables
    if (static_cast<double>(rand()) / RAND_MAX < negativeProbability) {
        literal = -literal; // Κάνουμε το literal αρνητικό
    }
    return literal;
}

// Έλεγχος εγκυρότητας όρου
bool isClauseValid(const vector<int>& clause) {
    unordered_set<int> seen;
    for (int literal : clause) {
        if (seen.count(-literal)) {
            return false; // Υπάρχει σύγκρουση (π.χ., P και ¬P)
        }
        if (seen.count(literal)) {
            return false; // Το ίδιο literal εμφανίζεται πάνω από μία φορά
        }
        seen.insert(literal);
    }
    return true;
}

// Μετατροπή όρου σε μοναδική μορφή string για έλεγχο διπλοτύπων
string clauseToString(const vector<int>& clause) {
    vector<int> sortedClause = clause;
    sort(sortedClause.begin(), sortedClause.end()); // Ταξινόμηση για αποφυγή ισοδύναμων όρων
    stringstream ss;
    for (int lit : sortedClause) {
        ss << lit << " ";
    }
    return ss.str();
}

// Δημιουργία μοναδικών, έγκυρων τυχαίων 3-SAT προβλημάτων
vector<vector<int>> generate3SATProblem() {
    vector<vector<int>> clauses(numClauses, vector<int>(3)); // Δισδιάστατος πίνακας C*3
    unordered_set<string> uniqueClauses;

    int clauseCount = 0;
    while (clauseCount < numClauses) {
        vector<int> clause(3);

        // Γεννήστε literals
        for (int i = 0; i < 3; ++i) {
            clause[i] = generateLiteral();
        }

        // Ελέγξτε αν ο όρος είναι έγκυρος
        if (!isClauseValid(clause)) {
            continue;
        }

        // Δημιουργήστε το string του όρου για έλεγχο μοναδικότητας
        string clauseStr = clauseToString(clause);

        if (uniqueClauses.count(clauseStr)) {
            continue; // Ήδη υπάρχει
        }

        // Προσθήκη όρου στη λίστα
        clauses[clauseCount] = clause; // Αποθήκευση στον πίνακα
        uniqueClauses.insert(clauseStr);
        clauseCount++;
    }

    return clauses;
}

// Εμφάνιση προβλήματος 3-SAT
void display3SATProblem(const vector<vector<int>>& clauses) {
    for (size_t i = 0; i < clauses.size(); ++i) {
        cout << "(";
        for (size_t j = 0; j < clauses[i].size(); ++j) {
            cout << (clauses[i][j] > 0 ? "x" : "¬x") << abs(clauses[i][j]);
            if (j < clauses[i].size() - 1) {
                cout << " ∨ ";
            }
        }
        cout << ")";
        if (i < clauses.size() - 1) {
            cout << " ∧ ";
        }
    }
    cout << endl;
}

// ---------------- Κύριο Πρόγραμμα ----------------

int main() {
    srand(static_cast<unsigned int>(time(0))); // Τυχαία αρχικοποίηση

    // Εισαγωγή παραμέτρων
    cout << "Εισάγετε το πλήθος των προβλημάτων: ";
    cin >> numProblems;
    cout << "Εισάγετε το πλήθος των μεταβλητών (N): ";
    cin >> numVariables;
    cout << "Εισάγετε το πλήθος των όρων (C): ";
    cin >> numClauses;
    cout << "Εισάγετε την πιθανότητα αρνητικού literal (π.χ. 0.5): ";
    cin >> negativeProbability;
    cout << "Εισάγετε το maxTries: ";
    cin >> maxTries;
    cout << "Εισάγετε το maxFlips: ";
    cin >> maxFlips;
    cout << "Εισάγετε την παράμετρο a (π.χ. 0.1): ";
    cin >> a;

    // Δημιουργία και εμφάνιση προβλημάτων
    for (int i = 0; i < numProblems; ++i) {
        cout << "Πρόβλημα 3-SAT " << i + 1 << ":\n";
        vector<vector<int>> problem = generate3SATProblem();
        display3SATProblem(problem);

        // Εμφάνιση των παραμέτρων για κάθε πρόβλημα
        cout << "\nΠαράμετροι:\n";
        cout << "maxTries: " << maxTries << "\n";
        cout << "maxFlips: " << maxFlips << "\n";
        cout << "a: " << a << "\n";

        cout << "\n\n";
    }

    return 0;
}