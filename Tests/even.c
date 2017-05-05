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


int decrement(int i) {
  int res;
  res = i - 1;
  return res;
}

int increment(int i) {
  int res;
  res = i + 1;
  return res;
}

int zero (int i) {
  while (i > 0) {
    i = i - 1;
  }
  while (i < 0) {
    i = i + 1;
  }
  return i;
}

bool isNatural(int i) {
  bool res;
  res= false;
  if (i > 0) {
    res = true;
  }
  return res;
}


