

cd src/frontend

Interface:  cargo run --package didc -- bind --target ts-native-interface ../../declarations/backend/backend.did > ./backend.d.ts

Wrapper: cargo run --package didc -- bind --target ts-native-wrapper ../../declarations/backend/backend.did > ./backend.ts