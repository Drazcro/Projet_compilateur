#include <stdbool.h>


int addition (int i, int j) {
  int result;
  result = i + j;
  return result;
}

bool isEqual(int i, int j) {
  bool res;
  res = false;
  if (i == j) {
    res = true;
  }
  return res;
}
