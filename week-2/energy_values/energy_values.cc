#include <cmath>
#include <iostream>
#include <vector>
#include <algorithm>

const double EPS = 1e-6;
const int PRECISION = 20;

typedef std::vector<double> Column;
typedef std::vector<double> Row;
typedef std::vector<Row> Matrix;


#ifdef DEBUG
const bool debug = true;
#else
const bool debug = false;
#endif

struct Equation {
    Equation(const Matrix &a, const Column &b): a(a), b(b) {}

  // Represents Ax = b
  Matrix a; // coefficent matrix
  Column b; // result vector
};


/* Represents a pair which is position in coefficent matrix */
struct Position {
  Position(int column, int row): column(column), row(row) {}

  int column;
  int row;
};

void print_vector(const std::string &label,std::vector<bool> v){
  if(!debug)
    return;
  
  std::cerr<<label<<":[";
  for(bool item : v)
    std::cerr<<" "<<item;
  std::cerr<<"]"<<std::endl;
}

void print_matrix(const Matrix &a, const Column &b,Position &pivot ) {
  if(!debug)
    return;
  int column_width = 8;
  
  for(int i = 0 ; i < a.size()+1;i++)
    fprintf(stderr,"---------");
  fprintf(stderr,"\n" );
  
  for(int i = 0 ; i < a.size(); i++) {
    for(int j = 0 ; j < a[i].size(); j++) {
      if(pivot.row == i && pivot.column == j)
        fprintf(stderr,"[%-+4.4f]",a[i][j]);
      else
        fprintf(stderr," %-+4.4f ",a[i][j]);
    }
    fprintf(stderr," |%-+4.4f ",b[i]);
    fprintf(stderr,"\n");
  }


  for(int i = 0 ; i < a.size()+1;i++)
    fprintf(stderr,"---------");
  fprintf(stderr,"\n" );
  
}

Equation ReadEquation() {
  int size;
  std::cin >> size;
  // Ax = b
  // a - Represents the coefficient matrix
  Matrix a(size, std::vector <double> (size, 0.0));
  // b - represents the result vector
  Column b(size, 0.0);
    
  for (int row = 0; row < size; ++row) {
    for (int column = 0; column < size; ++column)
      std::cin >> a[row][column];
    std::cin >> b[row];
  }
    
  return Equation(a, b);
}

/**
 *
 */
Position SelectPivotElement(Matrix &a, Column &b,std::vector <bool> &used_rows, std::vector <bool> &used_columns) {
  // This algorithm selects the first free element.
  // TODO You'll need to improve it to pass the problem.
  
  Position pivot_element(0, 0);
  
  if(debug) {
    print_vector("used_rows",used_rows);
    print_vector("used_columns",used_columns);
  }
  
  while (used_rows[pivot_element.row])
    ++pivot_element.row;

  while (used_columns[pivot_element.column])
    ++pivot_element.column;

  if(a[pivot_element.row][pivot_element.column] == 0){
    // we need to find a non zero eleement in this column and swap with this row.
    int switch_row = pivot_element.row;
    while(switch_row < used_rows.size() && a[switch_row][pivot_element.column] == 0)
      switch_row++;
    if(switch_row < used_rows.size()) {
      std::swap(a[pivot_element.row],a[switch_row]);
      std::swap(b[pivot_element.row],b[switch_row]);
    }
     
  }
  if(debug)
    std::cerr<<"pivot:["<<pivot_element.row<<","<<pivot_element.column<<"]"<<std::endl;
  
  return pivot_element;
}



void SwapLines(Matrix &a, Column &b, std::vector <bool> &used_rows, Position &pivot_element) {
  
    std::swap(a[pivot_element.column], a[pivot_element.row]);
    std::swap(b[pivot_element.column], b[pivot_element.row]);

    bool temp(used_rows[pivot_element.column]);
    used_rows[pivot_element.column] = used_rows[pivot_element.row];
    used_rows[pivot_element.row] = temp;
    
    // TODO Fix compilation error 
    //std::swap(used_rows[pivot_element.column], used_rows[pivot_element.row]);
    pivot_element.row = pivot_element.column;
}




void ProcessPivotElement(Matrix &a, Column &b, const Position &pivot_element) {
  // 1. Scale the row based on the pivot row.
  double value = a[pivot_element.row] [pivot_element.column];
  if(debug)
    std::cerr<<"Scaling by pivot value :"<<value<<std::endl;
  
  for(int i = 0 ; i < a[pivot_element.column].size(); i++)
    a[pivot_element.row][i] /= value;
  b[pivot_element.row] /= value;

  // 2. Now that the pivot position is 1 eliminate all elements in the column. 
  for(int i = 0 ; i< a.size() ; i++ ) { // for each row
    if( i == pivot_element.row)
      continue;
    int scale = -1*a[i][pivot_element.column]; // needed scaling
    for(int j = 0 ; j < a[i].size(); j++) {
      a[i][j] += scale*a[pivot_element.row][j];
    }
    b[i] += scale*b[pivot_element.row];
  }
}



void MarkPivotElementUsed(const Position &pivot_element, std::vector <bool> &used_rows, std::vector <bool> &used_columns) {
    used_rows[pivot_element.row] = true;
    used_columns[pivot_element.column] = true;
}




Column SolveEquation(Equation equation) {
  
  Matrix &a = equation.a;
  Column &b = equation.b;
  int size = a.size();

  /**
   * As we move thourgh the list of elements we will mark
   * them as used.
   */
  std::vector <bool> used_columns(size, false);
  std::vector <bool> used_rows(size, false);
    
  for (int step = 0; step < size; ++step) {
    if(debug) {
      std::cerr<<"step :"<<step<<std::endl;
    }
    
    Position pivot_element = SelectPivotElement(a,b, used_rows, used_columns);
    //Given position of pivot element
    SwapLines(a, b, used_rows, pivot_element);
    print_matrix(a,b,pivot_element);
    ProcessPivotElement(a, b, pivot_element);
    if(debug)
      std::cerr<<"After Process Pivot Element"<<std::endl;
    
    print_matrix(a,b,pivot_element);
    MarkPivotElementUsed(pivot_element, used_rows, used_columns);    
  }

  return b;
}

void PrintColumn(const Column &column) {
    int size = column.size();
    std::cout.precision(PRECISION);
    
    for (int row = 0; row < size; ++row)
        std::cout << column[row] << std::endl;
    
}

int main() {
    Equation equation = ReadEquation();
    Column solution = SolveEquation(equation);
    PrintColumn(solution);
    return 0;
}
