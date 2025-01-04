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
double p, a;

// Δημιουργία τυχαίου literal με βάση την πιθανότητα εμφάνισης αρνητικού literal
int generateLiteral() {
    int literal = rand() % numVariables + 1; // Από 1 έως numVariables
    if (static_cast<double>(rand()) / RAND_MAX < p) {
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
            cout << (clauses[i][j] > 0 ? "x" : "~x") << abs(clauses[i][j]);
            if (j < clauses[i].size() - 1) {
                cout << " OR ";
            }
        }
        cout << ")";
        if (i < clauses.size() - 1) {
            cout << " AND ";
        }
    }
    cout << endl;
}

// Υπολογισμός κόστους και μη ικανοποιημένων όρων
int computeCost(const vector<vector<int>>& clauses, const vector<int>& assignment, vector<int>& unsatisfiedClauses) {
    int cost = 0;
    unsatisfiedClauses.clear();

    for (size_t i = 0; i < clauses.size(); ++i) {
        bool satisfied = false;
        for (int literal : clauses[i]) {
            if ((literal > 0 && assignment[abs(literal) - 1] == 1) ||
                (literal < 0 && assignment[abs(literal) - 1] == 0)) {
                satisfied = true;
                break;
            }
        }
        if (!satisfied) {
            ++cost;
            unsatisfiedClauses.push_back(i);
        }
    }

    return cost;
}

// GSAT + RW
vector<int> gsatRW(const vector<vector<int>>& clauses, int maxTries, int maxFlips, double p) {
    vector<int> bestAssignment;
    int minCost = clauses.size();   //Αρχικοποίηση του κόστους με το πλήθος των όρων

    for (int t = 0; t < maxTries; ++t) {    //Επαναλήψεις προσπαθειών    
        vector<int> assignment(numVariables);
        for (int i = 0; i < numVariables; ++i) {
            assignment[i] = rand() % 2;     //Ανάθεση τιμής 0 ή 1
        }

        for (int f = 0; f < maxFlips; ++f) {
            vector<int> unsatisfiedClauses;
            int currentCost = computeCost(clauses, assignment, unsatisfiedClauses);

            if (currentCost == 0) {     //Αν δεν υπάρχει false όρος
                cout << "Cost: " << currentCost << endl;
                return assignment;      //επιστροφή λύσης 
            }

            int chosenVariable;
            if (static_cast<double>(rand()) / RAND_MAX < p) {
                int maxGain = -1;
                for (int i = 0; i < numVariables; ++i) {
                    int gain = 0;
                    for (int clauseIdx : unsatisfiedClauses) {
                        bool wouldBeSatisfied = false;
                        for (int literal : clauses[clauseIdx]) {
                            if ((literal > 0 && (assignment[abs(literal) - 1] ^ (literal == i + 1))) ||
                                (literal < 0 && (assignment[abs(literal) - 1] ^ (literal == -(i + 1))))) {
                                wouldBeSatisfied = true;
                                break;
                            }
                        }
                        if (wouldBeSatisfied) {
                            ++gain;
                        }
                    }
                    if (gain > maxGain) {
                        maxGain = gain;
                        chosenVariable = i;
                    }
                }
            } else {
                int randomClause = unsatisfiedClauses[rand() % unsatisfiedClauses.size()];
                chosenVariable = abs(clauses[randomClause][rand() % clauses[randomClause].size()]) - 1;
            }

            assignment[chosenVariable] = 1 - assignment[chosenVariable];

            if (currentCost < minCost) {
                minCost = currentCost;
                bestAssignment = assignment;
            }
        }
    }

    cout << "Cost: " << minCost << endl;
    return bestAssignment;
}

int main() {
    srand(static_cast<unsigned int>(time(0))); // Τυχαία αρχικοποίηση

    cout << "Enter the number of problems: ";
    cin >> numProblems;
    cout << "Enter the number of variables (N): ";
    cin >> numVariables;
    cout << "Enter the number of clauses (C): ";
    cin >> numClauses;
    cout << "Enter the probability p (0-1) (eg. 0.2): ";
    cin >> p;
    cout << "Enter maxTries: ";
    cin >> maxTries;
    cout << "Enter maxFlips: ";
    cin >> maxFlips;
    cout << "Enter parameter a (0-1) (eg. 0.8): ";
    cin >> a;

    if (numClauses > (numVariables * (numVariables-1) * (numVariables-2)) / 6) {
        cout << "Error: Too many clauses requested for given number of variables" << endl;
        return 1;
    }

    for (int i = 0; i < numProblems; ++i) {
        cout << "3-SAT Problem " << i + 1 << ":\n";
        vector<vector<int>> problem = generate3SATProblem();
        display3SATProblem(problem);

        vector<int> solution = gsatRW(problem, maxTries, maxFlips, a);

        if (!solution.empty()) {
            cout << "Solution found: ";
            for (int val : solution) {
                cout << val << " ";
            }
            cout << endl << endl;
        } else {
            cout << "No solution found." << endl;
        }
    }

    return 0;
}
