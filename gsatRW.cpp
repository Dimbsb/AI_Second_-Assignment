#include <iostream>
#include <vector>
#include <unordered_set>
#include <algorithm>
#include <cstdlib>
#include <ctime>
#include <sstream>
#include <stdexcept>

using namespace std;

// Global variables for parameters
int numProblems, numVariables, numClauses, maxTries, maxFlips;
double negativeProbability, a;

// Δημιουργία τυχαίου literal με ομοιόμορφη πιθανότητα
int generateLiteral() {
    double probability = 1.0 / (2 * numVariables); // Πιθανότητα για κάθε literal
    int randomNum = rand() % (2 * numVariables);
    int literal = (randomNum % numVariables) + 1;
    return (randomNum < numVariables) ? literal : -literal;
}

// Έλεγχος εγκυρότητας όρου
bool isClauseValid(const vector<int>& clause) {
    unordered_set<int> seen;
    for (int literal : clause) {
        if (seen.count(-literal) || seen.count(literal)) {
            return false;
        }
        seen.insert(literal);
    }
    return true;
}

// Μετατροπή όρου σε μοναδική μορφή string
string clauseToString(const vector<int>& clause) {
    vector<int> sortedClause = clause;
    sort(sortedClause.begin(), sortedClause.end());
    stringstream ss;
    for (int lit : sortedClause) {
        ss << lit << " ";
    }
    return ss.str();
}

// Έλεγχος εγκυρότητας παραμέτρων
void validateParameters() {
    if (numVariables <= 0 || numClauses <= 0 || maxTries <= 0 || maxFlips <= 0) {
        throw invalid_argument("All numeric parameters must be positive");
    }
    if (negativeProbability < 0 || negativeProbability > 1 || a < 0 || a > 1) {
        throw invalid_argument("Probabilities must be between 0 and 1");
    }
    // Έλεγχος για το μέγιστο αριθμό δυνατών μοναδικών όρων
    int maxPossibleClauses = (numVariables * (numVariables-1) * (numVariables-2)) / 6;
    if (numClauses > maxPossibleClauses) {
        throw invalid_argument("Too many clauses requested for given number of variables");
    }
}

// Δημιουργία 3-SAT προβλήματος
vector<vector<int>> generate3SATProblem() {
    vector<vector<int>> clauses(numClauses, vector<int>(3));
    unordered_set<string> uniqueClauses;

    int clauseCount = 0;
    int attempts = 0;
    const int MAX_ATTEMPTS = 1000000; // Αποφυγή ατέρμονου βρόχου

    while (clauseCount < numClauses && attempts < MAX_ATTEMPTS) {
        vector<int> clause(3);
        for (int i = 0; i < 3; ++i) {
            clause[i] = generateLiteral();
        }

        if (!isClauseValid(clause)) {
            attempts++;
            continue;
        }

        string clauseStr = clauseToString(clause);
        if (uniqueClauses.count(clauseStr)) {
            attempts++;
            continue;
        }

        clauses[clauseCount] = clause;
        uniqueClauses.insert(clauseStr);
        clauseCount++;
    }

    if (clauseCount < numClauses) {
        throw runtime_error("Failed to generate enough unique clauses");
    }

    return clauses;
}

// Υπολογισμός κόστους και μη ικανοποιημένων όρων
int computeCost(const vector<vector<int>>& clauses, const vector<int>& assignment, 
                vector<int>& unsatisfiedClauses) {
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

// GSAT + RW αλγόριθμος
vector<int> gsatRW(const vector<vector<int>>& clauses, int maxTries, int maxFlips, double p) {
    vector<int> bestAssignment;
    int bestCost = clauses.size();

    for (int t = 0; t < maxTries; ++t) {
        // Τυχαία αρχική ανάθεση
        vector<int> assignment(numVariables);
        for (int i = 0; i < numVariables; ++i) {
            assignment[i] = rand() % 2;
        }

        for (int f = 0; f < maxFlips; ++f) {
            vector<int> unsatisfiedClauses;
            int currentCost = computeCost(clauses, assignment, unsatisfiedClauses);

            if (currentCost == 0) {
                cout << "Solution found with cost: " << currentCost << endl;
                return assignment;
            }

            // Επιλογή μεταβλητής για flip
            int chosenVariable;
            if (static_cast<double>(rand()) / RAND_MAX < p) {
                int maxGain = -1;
                vector<int> bestVariables; // Για την περίπτωση ισοπαλίας

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
                        if (wouldBeSatisfied) ++gain;
                    }
                    
                    if (gain > maxGain) {
                        maxGain = gain;
                        bestVariables.clear();
                        bestVariables.push_back(i);
                    } else if (gain == maxGain) {
                        bestVariables.push_back(i);
                    }
                }
                
                // Τυχαία επιλογή μεταξύ των καλύτερων μεταβλητών
                chosenVariable = bestVariables[rand() % bestVariables.size()];
            } else {
                // Random Walk
                int randomClause = unsatisfiedClauses[rand() % unsatisfiedClauses.size()];
                chosenVariable = abs(clauses[randomClause][rand() % clauses[randomClause].size()]) - 1;
            }

            assignment[chosenVariable] = 1 - assignment[chosenVariable];

            if (currentCost < bestCost) {
                bestCost = currentCost;
                bestAssignment = assignment;
            }
        }
    }

    cout << "Best cost found: " << bestCost << endl;
    return bestAssignment;
}

int main() {
    try {
        srand(static_cast<unsigned int>(time(0)));

        cout << "Enter the number of problems: ";
        cin >> numProblems;
        cout << "Enter the number of variables (N): ";
        cin >> numVariables;
        cout << "Enter the number of clauses (C): ";
        cin >> numClauses;
        cout << "Enter the probability of a negative literal (0-1): ";
        cin >> negativeProbability;
        cout << "Enter maxTries: ";
        cin >> maxTries;
        cout << "Enter maxFlips: ";
        cin >> maxFlips;
        cout << "Enter parameter a (0-1): ";
        cin >> a;

        validateParameters();

        for (int i = 0; i < numProblems; ++i) {
            cout << "\n3-SAT Problem " << i + 1 << ":\n";
            vector<vector<int>> problem = generate3SATProblem();
            
            cout << "Problem formula:\n";
            for (size_t j = 0; j < problem.size(); ++j) {
                cout << "(";
                for (size_t k = 0; k < problem[j].size(); ++k) {
                    cout << (problem[j][k] > 0 ? "x" : "~x") << abs(problem[j][k]);
                    if (k < problem[j].size() - 1) cout << " OR ";
                }
                cout << ")";
                if (j < problem.size() - 1) cout << " AND ";
            }
            cout << "\n\n";

            vector<int> solution = gsatRW(problem, maxTries, maxFlips, a);

            if (!solution.empty()) {
                cout << "Solution: ";
                for (int val : solution) {
                    cout << val << " ";
                }
                cout << endl;
            } else {
                cout << "No solution found.\n";
            }
        }

    } catch (const exception& e) {
        cerr << "Error: " << e.what() << endl;
        return 1;
    }

    return 0;
}